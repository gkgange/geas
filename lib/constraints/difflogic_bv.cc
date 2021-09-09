#include <climits>
#include <unordered_map>

#include <geas/mtl/Heap.h>
#include <geas/utils/bitops.h>
#include <geas/solver/solver_debug.h>
#include <geas/solver/solver_data.h>
#include <geas/solver/solver_ext.h>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>
#include <geas/mtl/bool-set.h>
#include <geas/mtl/min-tree.h>

#define LATE_DIFFLOGIC
#define STRONGER_REDUNDANCY

using namespace geas;

// Re-implementation of the difference-logic propagator. Core algorithms
// are mostly the same, slightly neater checking of disentailment.

// For detecting bounds-based disentailment of suspended
// constraints.
struct susp_sep {
  struct cmp_sep {
    cmp_sep(vec<int>& _sep) : sep(_sep) { }

    bool operator()(int x, int y) const { return sep[x] < sep[y]; }
    vec<int>& sep;
  };

  susp_sep(void)
   : heap(cmp_sep(sep)) { }

  inline bool empty(void) const { return heap.empty(); }
  void add(int x) { heap.insert(x); }
  void update(int x) { heap.update(x); }
  void growTo(int sz) { sep.growTo(sz, 0); }

  vec<int> sep;
  vec<int> rel;
  Heap<cmp_sep> heap;
};

class diff_manager_bv : public propagator, public prop_inst<diff_manager_bv>, public solver_ext_nofree<diff_manager_bv> {
public:
  typedef unsigned int diff_id;
  typedef unsigned int dim_id;
  typedef unsigned int cst_id;
  typedef unsigned int rel_id;

  struct hash_dims {
    size_t operator()(const std::pair<dim_id,dim_id>& a) const {
      std::hash<dim_id> h;
      size_t seed = h(a.first);
      return (seed << 5) + seed + h(a.second);
    }
  };

  struct susp_xref {
    rel_id rel[32];
  };

  struct susp_cell {
    static susp_cell empty(int block, uint32_t mask = 0ul) {
      susp_cell cell({ block, mask, new susp_xref });
      return cell;
    }

    int block;
    uint32_t mask;
    susp_xref* xref;
  };

  enum { TRUE_CST = 0 };

  diff_manager_bv(solver_data* s)
    : propagator(s, PRIO_HIGH)
    , rseen_words(nullptr), rseen_end(nullptr), rseen_bits(nullptr)
    ,  fqueue(cmp_fwd_dist { this })
    ,  rqueue(cmp_rev_dist { this })
    , susp_trail_sz(0)
#ifdef REPORT_INTERNAL_STATS
    , lb_count(0), ub_count(0), bnd_count(0), diff_count(0)
#endif
  {
    // Trivial placeholder constraint
    csts.push(cst_info(-1, -1, INT_MAX, at_True, -1));
  }

  struct cmp_fwd_dist {
    bool operator()(dim_id x, dim_id y) const {
      if(d->fdist[x] - d->pot[x] == d->fdist[y] - d->pot[y])
        return d->flag[x] < d->flag[y];
      return d->fdist[x] - d->pot[x] < d->fdist[y] - d->pot[y];
    }
    diff_manager_bv* d;
  };
  struct cmp_rev_dist {
    bool operator()(dim_id x, dim_id y) const {
      if(d->rdist[x] + d->pot[x] == d->rdist[y] + d->pot[y])
        return d->flag[x] < d->flag[y];
      return d->rdist[x] + d->pot[x] < d->rdist[y] + d->pot[y];
    }
    diff_manager_bv* d;
  };

  //===================
  // Bookkeeping datastructures
  //===================
  // Difference constraint attachments
  // Constraint index 0 is a sentinel.
  struct cst_info {
    cst_info(int _s, int _d, int _wt, patom_t _act, rel_id _rel)
      : s(_s), d(_d), wt(_wt), act(_act)
      , sus_sep(0), diff_next(0), rel(_rel) { }

    dim_id s;
    dim_id d;
    int wt;

    patom_t act;

    int sus_sep; // Separator last time this was suspended.
    cst_id diff_next; // Next-tightest constraint with the same (s, d).
    rel_id rel;
  };

  // So that when we re-suspend a constraint,
  // we can adjust the state accordingly.
  struct susp_trail_entry {
    susp_trail_entry(cst_id _old, cst_id _act)
      : old_cst(_old), act_cst(_act) { }
    cst_id old_cst; // Which constraint are we putting back?
    cst_id act_cst; // Which active constraint (if any) are we changing?
  };

  // Information about currently enforced
  // constraints.
  struct rel_info {
    static rel_info no_cst(int s, int d) {
      rel_info diff = {
        INT_MAX,
        INT_MAX,
        TRUE_CST,

        0, 0, // fwd/rev crossreferences
        TRUE_CST,

        s,
        d
      };
      return diff;
    }

    int wt; // Currently enforced bound
    int sus_wt; // Tightest suspended constraint.

    cst_id cst; // ID of currently binding constraint.

    // Cross-references.
    int fwd_idx;
    int rev_idx;
    
    cst_id sus_cst;

    int s;
    int d;
    int lb_idx; // Index into lb/ub susp.
    int ub_idx;
    int susp_block; // Index into susp_fwd
  };

  struct act_edge {
    int wt;
    dim_id dim;
    int cst_id;
  };

  // Raw constraints
  vec<cst_info> csts;
  // Indexed by (s, d)
  //  vec< vec<diff_info> > diffs;
  vec<rel_info> rels;

  // Graph of currently active constraints.
  vec< vec<act_edge> > fwd;
  vec< vec<act_edge> > rev;

  // Bit-vector of forward-reachable edges with suspended
  // relations.
  // vec<uint64_t*> susp_succ; // s -> { d | s -> d in suspended }
  vec< vec<susp_cell> > susp_succ;

  // Managing satisfiability witnesses of
  // any suspended constraints.
  vec<susp_sep*> susp_lb;
  vec<susp_sep*> susp_ub;

  //======================
  // Transient bookkeeping
  //======================
  //// For detecting disentailed constraints.
  int* rseen_words;
  int* rseen_end;
  uint32_t* rseen_bits;

  vec<int> rseen_vars;
  vec<int> fseen_vars;

  //// Normal difference-logic bookkeeping
  // Potential function: for all active (x -(wt)-> y),
  // pot(y) + wt - pot(x) >= 0.
  vec<int> pot;

  // During forward/backward traversal. Should really factor these out.
  vec<bool> flag;
  vec<int> fdist;
  vec<int> fpred;
  boolset fseen;
  Heap<cmp_fwd_dist> fqueue;

  vec<int> rdist;
  vec<int> rpred;
  boolset rseen;
  Heap<cmp_rev_dist> rqueue;

#ifdef LATE_DIFFLOGIC
  vec<int> stackpred;
#endif
  
  //=====================
  // Persistence management
  //=====================
  vec<susp_trail_entry> susp_trail;
  Tuint susp_trail_sz;
  
  inline void bv_insert(int*& words, uint32_t* bits, int val) {
    int block = B32::block(val);
    if(!bits[block])
      *words++ = block;
    bits[block] |= B32::bit(val);
  }
  inline void bv_clear(int* words, int*& words_end, uint32_t* bits) {
    for(int w : range(words, words_end))
      bits[w] = 0;
    words_end = words;
  }

  // Having inferred that d - s >= wt, propagate and
  // remove any suspended constraints [d - s < wt].
  bool _process_suspended_rel(rel_id d, int wt, uint32_t& mask);
  inline bool process_suspended_rel(rel_id rel_id, int delta, uint32_t& mask) {
    // int wt = fdist[s] + rdist[d] - delta; // This is min diff from d to s.
    const rel_info& diff(rels[rel_id]);
    int wt = delta - fdist[diff.s] - rdist[diff.d]; // Which makes this the max from s to d.
    if(diff.sus_wt < wt)
      return _process_suspended_rel(rel_id, wt, mask);
    return true;
  }


  watch_result wake_r(int ci) {
    untrail();
    const cst_info& cst(csts[ci]);
    if(cst.wt < rels[cst.rel].wt) {
      act_queue.push(ci);
      queue_prop();
    }
    return Wt_Keep;
  }

  // Deactivate redundant constraints
  watch_result wake_dis(int c) {
    // TODO
    return Wt_Keep;
  }

  watch_result wake_lb(int di) {
    if(!lb_change.elem(di)) {
      lb_change.add(di);
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_ub(int di) {
    if(!ub_change.elem(di)) {
      ub_change.add(di);
      queue_prop();
    }
    return Wt_Keep;
  }

  void cleanup(void) {
    is_queued = false;
    act_queue.clear();
    lb_change.clear();
    ub_change.clear();
    //lb_check.clear();
    //ub_check.clear();
  }
  
  bool check_sat(ctx_t& ctx) {
    // The nothing-fancy approach: build the graph, and run Bellman-Ford to check for negative cycles.
    // Put the zero-vertex at the end.
    vec< std::tuple<dim_id, int, dim_id> > edges;
    vec<int> dists(vars.size(), 0);

    boolset seen(vars.size());
    for(cst_info& c : csts.tail()) {
      // Is the constraint active?
      patom_t at = c.act;
      if(at.lb(ctx)) {
        // First, check whether the bounds are consistent.
        if(vars[c.s].lb(ctx) - vars[c.d].ub(ctx) > c.wt)
          return false;

        // If so, add the edge to the graph.
        edges.push(std::make_tuple(c.s, c.wt, c.d));
        seen.add(c.s);
        seen.add(c.d);
      }
    }

    // Run Bellman-Ford.
    // fprintf(stderr, "%% %d edges.\n", edges.size() - 2 * vars.size());
    for(int it = 0; it <= seen.size(); ++it) {
      for(auto e : edges) {
        dim_id x(std::get<0>(e));
        int wt(std::get<1>(e));
        dim_id y(std::get<2>(e));

        dists[y] = std::max(dists[y], dists[x] - wt);
      }
    }
    // If no non-negative cycles, should have stabilised by now.
    for(auto e : edges) {
      dim_id x(std::get<0>(e));
      int wt(std::get<1>(e));
      dim_id y(std::get<2>(e));
      if(dists[y] < dists[x] - wt)
        return false;
    }
    return true;
  }

  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  bool propagate(vec<clause_elt>& confl) {
    // If we've backtracked since the last execution,
    // restore the state.
    // Don't need to untrail on failure, because any
    // changes will get reverted on the next run.
    untrail(); 

    // Process newly activated constraints.
    for(unsigned int ci : act_queue) {
      if(!activate(ci, confl))
        return false;
    }

    // Now bounds. Process active constraints
    // before processing suspended.
    for(dim_id v : lb_change) {
      if(!process_lb_change(v))
        return false;
    }
    for(dim_id v : ub_change) {
      if(!process_ub_change(v))
        return false;
    }

    // If we made it this far, commit to the changes.
    set(susp_trail_sz, (unsigned) susp_trail.size());
    return true;
  }

  // Post a new constraint r -> (x - y <= k)
  bool post(patom_t r, intvar x, intvar y, int k);

  // Propagate
  bool activate(cst_id c, vec<clause_elt>& confl);

  // Assumes these are only called inside activate, so
  // (f/r)seen, (f/r)dist are set up correctly
  // by fill_(f/r)dist
  bool process_suspended(int delta);
  bool process_act_bounds(dim_id s, dim_id d);

  void fill_rdist(dim_id s, dim_id d, int wt);
  void fill_fdist(dim_id s, dim_id d, int wt);

  bool process_lb_change(dim_id d);
  bool process_ub_change(dim_id d);
  bool process_suspended_lb(dim_id d);
  bool process_suspended_ub(dim_id d);

  bool process_killed(cst_id c, vec<clause_elt>& confl);
  bool propagate_if_killed(cst_id c, cst_id e, vec<clause_elt>& confl);
  
  inline void untrail(void) {
    if(susp_trail_sz != susp_trail.size())
      untrail_to(susp_trail_sz);
  }
  void untrail_to(unsigned sz);
  void suspend_cst(cst_id ci);
   
  bool repair_potential(dim_id s, dim_id d, int wt);
  bool exists_path(dim_id s0, dim_id d0, int cap);

  inline void queue_fwd(dim_id d, int wt, dim_id r);
  inline void queue_rev(dim_id d, int wt, dim_id r);

  void ex_lb(int tag, pval_t p, vec<clause_elt>& expl);
  void ex_ub(int tag, pval_t p, vec<clause_elt>& expl);
  void ex_r_bnd(int c, pval_t p, vec<clause_elt>& expl);
  void ex_r_diff(int c, pval_t p, vec<clause_elt>& expl);

  void report_internal(void);
  
  dim_id get_dim(intvar x);
  rel_id get_rel(dim_id x, dim_id y);

  vec<intvar> vars;

  // Changes to deal with when the propagator runs.
  vec<unsigned int> act_queue; // Which activations have occurred 
  boolset lb_change; //boolset lb_check;
  boolset ub_change; //boolset ub_check;

#ifdef REPORT_INTERNAL_STATS
  int lb_count;
  int ub_count;
  int bnd_count;
  int diff_count;
#endif

  // Mapping variables to dimensions
  std::unordered_map<geas::pid_t, dim_id> dim_map;
  std::unordered_map< std::pair<dim_id, dim_id>, rel_id, hash_dims> rel_map;
};

// Posting x - y <= k
bool diff_manager_bv::post(patom_t r, intvar x, intvar y, int k) {
  // If the constraint is already deactivated,
  // forget it.
  if(!r.ub(s->ctx()))
    return true;

  // First, find the dimensions corresponding to some offset of x.
  dim_id dx(get_dim(x));
  dim_id dy(get_dim(y));
  rel_id rel(get_rel(dx, dy));
  assert(vars[dx].p == x.p);
  assert(vars[dy].p == y.p);

  // Reformulate the constraint in terms of our dimensions.
  k += (vars[dx].off - x.off); // if x is shifted higher, constraint is tighter.
  k -= (vars[dy].off - y.off);

  // diff_info& di(get_info(dx, dy));
  rel_info& di(rels[rel]);

  // If the constraint is already entailed, we can
  // ignore it.
  if(di.wt <= k)
    return true;

  if(lb(vars[dx]) - ub(vars[dy]) > k) {
    if(!enqueue(*s, ~r, reason()))
      return false;
  }
  if(r.lb(s->ctx())) {
    // Already active. Just a globally true edge.
    if(pot[dx] + k - pot[dy] < 0 && !repair_potential(dx, dy, k))
      return false;

    // Check if there's already a constraint posted.
    if(di.cst) {
      assert(di.cst != 0);
      fwd[dx][di.fwd_idx].wt = k;
      rev[dy][di.rev_idx].wt = k;
      csts[di.cst].wt = k;
      csts[di.cst].act = r;
    } else {
      int ci = csts.size();
      csts.push(cst_info(dx, dy, k, r, rel));
      di.cst = ci;
      di.fwd_idx = fwd[dx].size();
      di.rev_idx = rev[dy].size();
      fwd[dx].push(act_edge { k, dy, ci });
      rev[dy].push(act_edge { k, dx, ci });
    }
    di.wt = k;

    lb_change.add(dx);
    ub_change.add(dy);
    // TODO: check that we haven't missed any
    // inferences.
  } else {
    cst_id ci = csts.size();
    csts.push(cst_info(dx, dy, k, r, rel));

    // Suspended. Set up all the data-structures.
    attach(s, r, watch<&P::wake_r>(ci));

    // Chosen separator.
    int m = lb(vars[dx]) + (ub(vars[dy]) - k - lb(vars[dx]))/2;
    csts[ci].sus_sep = m;

    // Insert ci into the ordered list of constraints on (dx, dy).
    if(k <= di.sus_wt) {
      csts[ci].diff_next = di.sus_cst;
      if(di.sus_wt == INT_MAX) {
        // If this is the first suspended constraint, set up the
        // crossreferences.
        int lb_idx = susp_lb[dx]->sep.size();
        susp_lb[dx]->sep.push();
        susp_lb[dx]->rel.push(rel);
        di.lb_idx = lb_idx;
        int ub_idx = susp_ub[dy]->sep.size();
        susp_ub[dy]->sep.push();
        susp_ub[dy]->rel.push(rel);
        di.ub_idx = ub_idx;

        auto& s_succ(susp_succ[dx]);
        int d_block = B32::block(dy);
        // uint32_t d_bit = B32::bit(dy);
        unsigned susp_idx = 0;
        for(susp_cell& cell : s_succ) {
          if(cell.block == d_block)
            goto susp_idx_found;
          ++susp_idx;
        }
        // If we fell through, create a new one.
        s_succ.push(susp_cell::empty(d_block));
    susp_idx_found:
        s_succ[susp_idx].xref->rel[B32::index(dy)] = rel;
        di.susp_block = susp_idx;
      }
      suspend_cst(ci);
    } else {
      // Insert this in the correct place
      int pred = di.sus_cst;
      int next = csts[pred].diff_next;
      while(csts[next].wt < k) {
        pred = next;
        next = csts[pred].diff_next;
      }
      csts[pred].diff_next = ci;
      csts[ci].diff_next = next;
    }

    // assert(lb(vars[dx]) <= dims[dx].threshold_lb.root_val());
    // assert(-dims[dy].threshold_ub.root_val() <= ub(vars[dy]));
    // check_witnesses();
  }
  return true;
}

bool diff_manager_bv::activate(cst_id ci, vec<clause_elt>& confl) {
  // Check if we're directly inconsistent.
  const cst_info& cst(csts[ci]);
  // diff_info& diff(get_info(cst.s, cst.d));
  rel_info& diff(rels[cst.rel]);

  // If the constraint is already entailed,
  // skip it.
  if(diff.wt <= cst.wt)
    return true;
  if(vars[cst.s].ub(s) - vars[cst.d].lb(s) <= cst.wt)
    return true;

#ifndef LATE_DIFFLOGIC
  if(pot[cst.s] + cst.wt - pot[cst.d] < 0 &&
     !repair_potential(cst.s, cst.d, cst.wt)) {
    // Collect the corresponding failure, and abort.
    EX_PUSH(confl, ~cst.act);
    // FIXME
    dim_id d_r(cst.s);
    do {
      cst_id c_r(fpred[d_r]);
      // rel_info curr(get_info(c_r, d_r));
      EX_PUSH(confl, ~csts[c_r].act);
      d_r = csts[c_r].s;
    } while (d_r != cst.d);
    return false;
  }

  // Need to fill rdist first, otherwise everything
  // always looks redundant.
  rpred[cst.s] = ci;
  fill_rdist(cst.s, cst.d, cst.wt);
  if(rseen_vars.size() == 0) {
    rseen_vars.clear();
    return true;
  }
  fpred[cst.d] = ci;
  fill_fdist(cst.s, cst.d, cst.wt);
#endif
  susp_trail.push(susp_trail_entry(diff.cst, ci));

  if(diff.cst) {
    fwd[cst.s][diff.fwd_idx].wt = cst.wt;
    fwd[cst.s][diff.fwd_idx].cst_id = ci;
    rev[cst.d][diff.rev_idx].wt = cst.wt;
    rev[cst.d][diff.rev_idx].cst_id = ci;
  } else {
    diff.fwd_idx = fwd[cst.s].size();
    diff.rev_idx = rev[cst.d].size();
    fwd[cst.s].push(act_edge { cst.wt, cst.d, ci });
    rev[cst.d].push(act_edge { cst.wt, cst.s, ci });
  }
  diff.wt = cst.wt;
  diff.cst = ci;

  // If nothing got closer, the constraint
  // we attempted to add was redundant.

  bool okay = true;
#ifdef LATE_DIFFLOGIC
  // Just enqueue the source and destination.
  int d_lb = lb(vars[cst.s]) - cst.wt;
  if(d_lb > lb(vars[cst.d])) {
    if(!set_lb(vars[cst.d], d_lb, expl<&P::ex_lb>(ci)))
      return false;
    if(!lb_change.elem(cst.d))
      lb_change.add(cst.d);
  }
  int s_ub = ub(vars[cst.d]) + cst.wt;
  if(ub(vars[cst.s]) > s_ub) {
    if(!set_ub(vars[cst.s], s_ub, expl<&P::ex_ub>(ci)))
      return false;
    if(!ub_change.elem(cst.s))
      ub_change.add(cst.s);
  }
#else
  // Set up the bitmap for process_suspended.
  for(int v : rseen_vars)
    bv_insert(rseen_end, rseen_bits, v);
  okay = process_suspended(cst.wt)
    && process_act_bounds(cst.s, cst.d);

  // Clear transient state
  bv_clear(rseen_words, rseen_end, rseen_bits);
  rseen_vars.clear();
  fseen_vars.clear();
#endif

  return okay;
}

void diff_manager_bv::fill_rdist(dim_id s, dim_id d, int wt) {
  // Run backward pass to compute
  // relevant nodes. Flag indicates whether it
  // passed through the new edge.
  int flag_count = 1;
  rdist[d] = 0; flag[d] = 0; rseen.add(d); rqueue.insert(d);
  rdist[s] = wt; flag[s] = 1; rseen.add(s); rqueue.insert(s);
  // rpred[s] = d; // Set in the caller, to avoid an extra argument.
  while(!rqueue.empty()) {
    dim_id d(rqueue.removeMin());
    int d_wt = rdist[d];
    if(flag[d]) {
      rseen_vars.push(d);
    }
    for(act_edge act : rev[d]) {
      int pred = act.dim;
      int pred_wt = act.wt;
      if(!rseen.elem(pred)) {
        flag_count += flag[d];
        rdist[pred] = d_wt + pred_wt; flag[pred] = flag[d];
        rpred[pred] = act.cst_id;
        rseen.add(pred); rqueue.insert(pred); 
      } else {
        if(d_wt + pred_wt < rdist[pred]) {
          assert(rqueue.inHeap(pred));
          flag_count += flag[d] - flag[pred];
          rdist[pred] = d_wt + pred_wt; flag[pred] = flag[d];
          rpred[pred] = act.cst_id;
          rqueue.decrease(pred);
        } else if(d_wt + pred_wt == rdist[pred] && flag[d] < flag[pred]) {
          assert(rqueue.inHeap(pred));
          flag_count += flag[d] - flag[pred];
          flag[pred] = flag[d];
          rpred[pred] = act.cst_id;
          rqueue.decrease(pred);
        }
      }
      flag_count -= flag[d];
      flag[d] = 0;
      if(!flag_count) {
        rqueue.clear();
        break;
      }
    }
  }
  rseen.clear();
}

void diff_manager_bv::fill_fdist(dim_id s, dim_id d, int wt) {
  int flag_count = 1;
  fdist[s] = 0; flag[s] = 0; fseen.add(s); fqueue.insert(s);
  fdist[d] = wt; flag[d] = 1; fseen.add(d); fqueue.insert(d);
  // fpred[d] = s; // Set in the caller, to avoid passing ci.
  while(!fqueue.empty()) {
    dim_id s(fqueue.removeMin());
    int s_wt = fdist[s];
    if(flag[s]) {
      fseen_vars.push(s);
    }
    for(act_edge act : fwd[s]) {
      int succ = act.dim;
      int succ_wt = act.wt;
      if(!fseen.elem(succ)) {
        fdist[succ] = s_wt + succ_wt; flag[succ] = flag[s];
        fpred[succ] = act.cst_id;
        fseen.add(succ); fqueue.insert(succ);
        flag_count += flag[s];
      } else {
        if(s_wt + succ_wt < fdist[succ]) {
          assert(fqueue.inHeap(succ));
          flag_count += flag[s] - flag[succ];
          fdist[succ] = s_wt + succ_wt; flag[succ] = flag[s];
          fpred[succ] = act.cst_id;
          fqueue.decrease(succ);
        } else if(s_wt + succ_wt == fdist[succ] && flag[s] < flag[succ]) {
          flag_count += flag[s] - flag[succ];
          flag[succ] = flag[s];
          fpred[succ] = act.cst_id;
          fqueue.decrease(succ);
        }
      }
    }
    flag_count -= flag[s];
    flag[s] = 0;
    if(!flag_count) {
      fqueue.clear();
      break;
    }
  }
  fseen.clear();
}

// If ub(t) changed, it must have been due to ub(d),
// and the minimum-slack chain. If we process them in
// the order they were popped off the queue, we just
// need to look at rpred.
bool diff_manager_bv::process_act_bounds(dim_id s, dim_id d) {
  int r_ub = ub(vars[d]);
  for(int r_s : rseen_vars) {
    int r_cst = rpred[r_s];

    int s_ub = r_ub + rdist[r_s];
    if(ub(vars[r_s]) > s_ub) {
#ifdef REPORT_INTERNAL_STATS
      ub_count++;
#endif
      if(!set_ub(vars[r_s], s_ub,
                 expl<&P::ex_ub>(r_cst)))
        return false;
    }
  }
  int f_lb = lb(vars[s]);
  for(int f_d : fseen_vars) {
    int f_cst = fpred[f_d];

    int d_lb = f_lb - fdist[f_d];
    if(lb(vars[f_d]) < d_lb) {
#ifdef REPORT_INTERNAL_STATS
      lb_count++;
#endif
      if(!set_lb(vars[f_d], d_lb,
                 expl<&P::ex_lb>(f_cst)))
        return false;
    }
  }
  return true;
}

// Assumes rseen and fseen are filled.
bool diff_manager_bv::process_suspended(int delta) {
  for(int d : rseen_vars)
    bv_insert(rseen_end, rseen_bits, d);
  
  for(int s : fseen_vars) {

    // Look only at the potential successors of s which
    // got tighter through the new edge (in rseen)
    for(susp_cell& cell : susp_succ[s]) {
      if(rseen_bits[cell.block] & cell.mask) {
        int32_t word = rseen_bits[cell.block] & cell.mask;
        while(word) {
          unsigned offset = __builtin_ctzl(word);
          word &= (word-1);

          int rel = cell.xref->rel[offset];
          if(!process_suspended_rel(rel, delta, cell.mask)) {
            bv_clear(rseen_words, rseen_end, rseen_bits);
            return false;
          }
        }
      }
    }
  }
  bv_clear(rseen_words, rseen_end, rseen_bits);
  return true;
}

bool diff_manager_bv::_process_suspended_rel(rel_id rel, int wt, uint32_t& mask) {
  rel_info& diff(rels[rel]);
  dim_id s(diff.s);
  dim_id d(diff.d);
  assert(susp_succ[s][diff.susp_block].mask & B32::bit(d));

  cst_id sus(diff.sus_cst);
  if(csts[sus].wt < wt) {
    // int sus0 = sus;
    do {
        // Current edge inconsistent.
        int idx = susp_trail.size();
        susp_trail.push(susp_trail_entry(sus, 0));
        cst_info& curr(csts[sus]);
        if(ub(curr.act)) {
#ifdef REPORT_INTERNAL_STATS
          diff_count++;
#endif
          if(!enqueue(*this->s, ~curr.act, expl<&P::ex_r_diff>(idx)))
            return false;
        }
        sus = curr.diff_next;
    } while(csts[sus].wt < wt);
    // susp_trail.push(susp_trail_entry(sus0, 0));
    diff.sus_cst = sus;
    diff.sus_wt = csts[sus].wt;
  }

  if(csts[sus].wt >= diff.wt) {
    // The remaining suspended constraints are entailed.
    // susp_succ[s][B64::block(d)] &= ~B64::bit(d);
    mask &= ~B32::bit(d);
    susp_lb[s]->heap.remove(diff.lb_idx);
    susp_ub[d]->heap.remove(diff.ub_idx);
  }
  return true;
}

// Process a lower bound change. Just doing it in a depth-first
// fashion.
bool diff_manager_bv::process_lb_change(dim_id s) {
  int s_lb = lb(vars[s]);
  for(act_edge act : fwd[s]) {
    if(lb(vars[act.dim]) < s_lb - act.wt) {
#ifdef REPORT_INTERNAL_STATS
        lb_count++;
#endif

#ifdef LATE_DIFFLOGIC
        if(stackpred[act.dim]) {
          // Inconsistent.
          vec<clause_elt>& confl(this->s->infer.confl);
          confl.clear();
          int curr = s;
          while(curr != act.dim) {
            int pred_id = stackpred[curr];
            EX_PUSH(confl, ~csts[pred_id].act);
            curr = csts[pred_id].s;
          }
          EX_PUSH(confl, ~csts[act.cst_id].act);
          return false;
        }
#endif

      if(!set_lb(vars[act.dim], s_lb - act.wt,
                 expl<&P::ex_lb>(act.cst_id)))
        return false;
#ifdef LATE_DIFFLOGIC
      stackpred[act.dim] = act.cst_id;
#endif
      bool okay = process_lb_change(act.dim);
#ifdef LATE_DIFFLOGIC
      stackpred[act.dim] = 0;
#endif
      if(!okay) return false;
    }
  }

  return process_suspended_lb(s);
}

bool diff_manager_bv::process_suspended_lb(dim_id s) {
  // Now check the suspended constraints.
  int s_lb = lb(vars[s]);
  int s_ub = ub(vars[s]);
  auto& s_susp(*susp_lb[s]);
  while(!s_susp.heap.empty()) {
    int rel_idx = s_susp.heap.getMin();
    rel_id rel = s_susp.rel[rel_idx];
    rel_info& diff(rels[rel]);
    int d = diff.d;

    if(s_lb <= s_susp.sep[rel_idx])
      break;

    int d_ub = ub(vars[d]);
    int d_lb = lb(vars[d]);
    int diff_min = s_lb - d_ub;
    //    diff_info& diff(get_info(s, d));
    int sus_wt = diff.sus_wt;
    int sus_cst = diff.sus_cst;
    int diff_max = std::min(diff.wt, (int) (s_ub - lb(vars[d])));
    if(sus_wt < diff_min) {
      csts[sus_cst].sus_sep = s_susp.sep[rel_idx];
      susp_trail.push(susp_trail_entry(sus_cst, 0));

      // Deactivate any newly invalid constraints.
      do {
#ifdef REPORT_INTERNAL_STATS
        bnd_count++;
#endif
        if(!enqueue(*this->s, ~csts[sus_cst].act, expl<&P::ex_r_bnd>(sus_cst, expl_thunk::Ex_BTPRED)))
          return false;
        sus_cst = csts[sus_cst].diff_next;
        sus_wt = csts[sus_cst].wt;
      } while(sus_wt < diff_min);
      diff.sus_wt = sus_wt;
      diff.sus_cst = sus_cst;

      if(diff_max <= sus_wt) {
        // Remaining suspended constraints are redundant.
        s_susp.heap.removeMin();
        susp_ub[d]->heap.remove(diff.ub_idx);
        susp_succ[s][diff.susp_block].mask &= ~B32::bit(d);
        continue;
      }
    } else if(diff_max <= sus_wt) {
#ifdef STRONGER_REDUNDANCY
      // Remaining suspended constraints are redundant.
      csts[sus_cst].sus_sep = s_susp.sep[rel_idx];
      susp_trail.push(susp_trail_entry(sus_cst, 0));
      s_susp.heap.removeMin();
      susp_ub[d]->heap.remove(diff.ub_idx);
      susp_succ[s][diff.susp_block].mask &= ~B32::bit(d);
      continue;
#endif
    }
    assert(sus_wt >= diff_min);

    // For now, put the threshold tight against the ub.
    int sep_new = d_ub + sus_wt;
    s_susp.sep[rel_idx] = sep_new;
    assert(sep_new >= vars[s].lb(this->s));
    //s_susp.heap.percolateDown(0);
    s_susp.heap.increase_(rel_idx);
    susp_ub[d]->sep[diff.ub_idx] = -d_ub;
    assert(-d_ub >= -vars[d].ub(this->s));
    susp_ub[d]->heap.decrease(diff.ub_idx);
  }

  return true;
}

bool diff_manager_bv::process_ub_change(dim_id d) {
  int d_ub = ub(vars[d]);
  for(act_edge act : rev[d]) {
    if(ub(vars[act.dim]) > d_ub + act.wt) {
#ifdef REPORT_INTERNAL_STATS
        ub_count++;
#endif

#ifdef LATE_DIFFLOGIC
        if(stackpred[act.dim]) {
          // Inconsistent cycle
          vec<clause_elt>& confl(this->s->infer.confl);
          confl.clear();
          int curr = d;
          while(curr != act.dim) {
            int succ_id = stackpred[curr];
            EX_PUSH(confl, ~csts[succ_id].act);
            curr = csts[succ_id].s;
          }
          EX_PUSH(confl, ~csts[act.cst_id].act);
          return false;
        }
#endif
      if(!set_ub(vars[act.dim], d_ub + act.wt,
                 expl<&P::ex_ub>(act.cst_id)))
        return false;

#ifdef LATE_DIFFLOGIC
      stackpred[act.dim] = act.cst_id;
#endif
      bool okay = process_ub_change(act.dim);
#ifdef LATE_DIFFLOGIC
      stackpred[act.dim] = 0;
#endif
      if(!okay) return false;
    }
  }

  return process_suspended_ub(d);
}

bool diff_manager_bv::process_suspended_ub(dim_id d) {
  int d_ub = ub(vars[d]);
  int d_lb = lb(vars[d]);
  auto& d_susp(*susp_ub[d]);
  while(!d_susp.heap.empty()) {
    // int s = d_susp.heap.getMin();
    int rel_idx = d_susp.heap.getMin();
    rel_id rel = d_susp.rel[rel_idx];
    rel_info& diff(rels[rel]);
    int s = diff.s;

    if(d_ub >= -d_susp.sep[rel_idx])
      break;

    int s_lb = lb(vars[s]);
    int diff_min = s_lb - d_ub;
    //    diff_info& diff(get_info(s, d));
    int sus_wt = diff.sus_wt;
    int sus_cst = diff.sus_cst;
    int diff_max = std::min(diff.wt, (int) (ub(vars[s]) - d_lb));
    if(sus_wt < diff_min) {
      csts[sus_cst].sus_sep = -d_susp.sep[rel_idx] + sus_wt;
      susp_trail.push(susp_trail_entry(sus_cst, 0));

      // Deactivate any newly invalid constraints.
      do {
#ifdef REPORT_INTERNAL_STATS
        bnd_count++;
#endif
        if(!enqueue(*this->s, ~csts[sus_cst].act, expl<&P::ex_r_bnd>(sus_cst, expl_thunk::Ex_BTPRED)))
          return false;
        sus_cst = csts[sus_cst].diff_next;
        sus_wt = csts[sus_cst].wt;
      } while(sus_wt < diff_min);
      diff.sus_wt = sus_wt;
      diff.sus_cst = sus_cst;

      if(diff_max <= sus_wt) {
        // Remaining suspended constraints are redundant.
        d_susp.heap.removeMin();
        susp_lb[s]->heap.remove(diff.lb_idx);
        susp_succ[s][diff.susp_block].mask &= ~B32::bit(d);
        continue;
      }
    } else if(diff_max <= sus_wt) {
#ifdef STRONGER_REDUNDANCY
      // Remaining suspended constraints are redundant.
      csts[sus_cst].sus_sep = -d_susp.sep[rel_idx] + sus_wt;
      susp_trail.push(susp_trail_entry(sus_cst, 0));
      d_susp.heap.removeMin();
      susp_lb[s]->heap.remove(diff.lb_idx);
      susp_succ[s][diff.susp_block].mask &= ~B32::bit(d);
      continue;
#endif
    }
    assert(sus_wt >= diff_min);
                            
    // For now, put the threshold tight against the ub.
    int sep_new = s_lb;
    d_susp.sep[rel_idx] = -sep_new +sus_wt;
    assert(d_susp.sep[rel_idx] >= -vars[d].ub(this->s));
    d_susp.heap.increase_(rel_idx);
    susp_lb[s]->sep[diff.lb_idx] = s_lb;
    assert(s_lb >= vars[s].lb(this->s));
    susp_lb[s]->heap.decrease(diff.lb_idx);
  }
  return true;
}

void diff_manager_bv::suspend_cst(cst_id ci) {
  // Backtracking past the point where a constraint was
  // enforced or disentailed.
  const cst_info& cst(csts[ci]);
  // diff_info& diff(get_info(cst.s, cst.d));
  rel_info& diff(rels[cst.rel]);

  // The following can be violated, if we're untrailing because
  // disentailment failed (so we never updated diff.sus_wt).
  // assert(cst.wt <= diff.sus_wt);

  diff.sus_wt = cst.wt;
  // Not necessarily true, because we're untrailing
  // after some domain changes happened.
  // assert(cst.sus_sep >= vars[cst.s].lb(s));
  // assert(-cst.sus_sep + cst.wt >= -vars[cst.d].ub(s));
  susp_lb[cst.s]->sep[diff.lb_idx] = cst.sus_sep;
  susp_ub[cst.d]->sep[diff.ub_idx] = -cst.sus_sep + cst.wt;
  susp_lb[cst.s]->update(diff.lb_idx);
  susp_ub[cst.d]->update(diff.ub_idx);
  susp_succ[cst.s][diff.susp_block].mask |= B32::bit(cst.d);
  diff.sus_cst = ci;
}

void diff_manager_bv::untrail_to(unsigned sz) {
  auto it(susp_trail.begin() + sz);
  auto en(susp_trail.end());
  while(it != en) {
    --en;
    // Re-insert these into the suspended-constraint
    // tracking.
    susp_trail_entry entry(*en);
    if(entry.act_cst) {
      // We're replacing an active constraint.
      const cst_info& cst(csts[entry.act_cst]);
      // diff_info& diff(get_info(cst.s, cst.d));
      rel_info& diff(rels[cst.rel]);

      if(entry.old_cst) {
        // Weakening.
        int new_wt = csts[entry.old_cst].wt;
        diff.wt = new_wt;
        diff.cst = entry.old_cst;
        fwd[cst.s][diff.fwd_idx].wt = new_wt;
        fwd[cst.s][diff.fwd_idx].cst_id = entry.old_cst;
        rev[cst.d][diff.rev_idx].wt = new_wt;
        rev[cst.d][diff.rev_idx].cst_id = entry.old_cst;
      } else {
        // Removal (and suspension)
        diff.wt = INT_MAX;
        diff.cst = 0;
        assert(diff.fwd_idx == fwd[cst.s].size()-1);
        assert(diff.rev_idx == rev[cst.d].size()-1);
        assert(fwd[cst.s].last().dim == cst.d);
        assert(rev[cst.d].last().dim == cst.s);
        fwd[cst.s].pop();
        rev[cst.d].pop();
      }
      if(cst.wt < diff.sus_wt)
        suspend_cst(entry.act_cst);
    } else {
      suspend_cst(entry.old_cst);
    }
  }
  susp_trail._size() = sz;
}
                                        
// ===========
// Explanation
// ===========
void diff_manager_bv::ex_lb(int ci, pval_t p, vec<clause_elt>& expl) {
  const cst_info& cst(csts[ci]);
  // Explaining the dest vertex lb.
  int ex_lb = vars[cst.d].lb_of_pval(p);
  EX_PUSH(expl, ~cst.act);
  EX_PUSH(expl, vars[cst.s] < ex_lb + cst.wt);
}

void diff_manager_bv::ex_ub(int ci, pval_t p, vec<clause_elt>& expl) {
  const cst_info& cst(csts[ci]);
  // Explaining the source vertex ub.
  int ex_ub = vars[cst.s].ub_of_pval(p);
  EX_PUSH(expl, ~cst.act);
  EX_PUSH(expl, vars[cst.d] > ex_ub - cst.wt);
}

// r was deactivated because lb(cst.s) - ub(cst.d) > cst.wt
void diff_manager_bv::ex_r_bnd(int ci, pval_t p, vec<clause_elt>& expl) {
  const cst_info& cst(csts[ci]);
  // Usually some flex in the separator value.
  // How do we pick it best?
  int sep = lb(vars[cst.s]);
  EX_PUSH(expl, vars[cst.s] < sep);
  EX_PUSH(expl, vars[cst.d] >= sep - cst.wt);
}

void diff_manager_bv::ex_r_diff(int tag, pval_t p, vec<clause_elt>& expl) {
  // tag is an index into susp_trail. Allows us to reset the graph state.
  int ci = susp_trail[tag].old_cst;
  const cst_info& cst(csts[ci]);

  untrail_to(tag);
  // Find some path such that adding c would introduce a negative cycle
  if(!exists_path(cst.d, cst.s, - cst.wt - 1))
    GEAS_ERROR;
  // Now collect the explanation
  dim_id curr(cst.s);
  while(curr != cst.d) {
    cst_id c_r = fpred[curr];
    EX_PUSH(expl, ~csts[c_r].act);
    curr = csts[c_r].s;
  }
}

// Need to compute new potential pot' s.t. pot'[d] + wt - pot[s] >= 0.
bool diff_manager_bv::repair_potential(dim_id s, dim_id d, int wt) {
  // Compute the change in potential.
  // We offset all weights by - pot[d], so the correction in cmp_fwd_dist
  // gives us the correct gamma.
  // As a result, dist[d] is exactly pot'[d].
  assert(fseen.size() == 0);
  assert(fqueue.empty());
  fdist[d] = pot[s] + wt;
  assert(fdist[d] < 0);
  fseen.add(d);
  fqueue.insert(d);

  while(!fqueue.empty()) {
    int r = fqueue.removeMin();
    int p = fdist[r];
    for(act_edge act : fwd[r]) {
      if(!fseen.elem(act.dim)) {
        if(p + act.wt - pot[act.dim] >= 0)
          continue;
        fpred[act.dim] = act.cst_id;
        if(act.dim == s) {
          // Found a negative weight loop from d to s.
          // fpred[s] = r;
          fseen.clear();
          fqueue.clear();
          return false;
        }
        fdist[act.dim] = p + act.wt;
        fseen.add(act.dim);
        fqueue.insert(act.dim);
      } else {
        if(p + act.wt < fdist[act.dim]) {
          assert(fqueue.inHeap(act.dim));
          fdist[act.dim] = p + act.wt;
          fpred[act.dim] = act.cst_id;
          fqueue.decrease(act.dim);
        }
      }
    }
  }

  // Successfully computed; update pot.
  for(dim_id p : fseen)
    pot[p] = fdist[p];

  assert(pot[s] + wt - pot[d] >= 0);
  // check_potential();

  fseen.clear();
  return true;
}

// Queue management during traversal.
inline void diff_manager_bv::queue_fwd(dim_id d, int wt, cst_id r) {
  if(fseen.elem(d)) {
    if(wt < fdist[d]) {
      assert(fqueue.inHeap(d));
      fdist[d] = wt;
      fpred[d] = r;
      fqueue.decrease(d);
    }
  } else {
    fdist[d] = wt;
    fpred[d] = r;
    fseen.add(d);
    fqueue.insert(d);
  }
}
inline void diff_manager_bv::queue_rev(dim_id d, int wt, cst_id r) {
  if(rseen.elem(d)) {
    if(wt < rdist[d]) {
      assert(rqueue.inHeap(d));
      rdist[d] = wt;
      rpred[d] = r;
      rqueue.decrease(d);
    }
  } else {
    rdist[d] = wt;
    rpred[d] = r;
    rseen.add(d);
    rqueue.insert(d);
  }
}

bool diff_manager_bv::exists_path(dim_id s0, dim_id d0, int cap) {
  assert(fseen.size() == 0);
  assert(rseen.size() == 0);
  assert(fqueue.empty());
  assert(rqueue.empty());
#if 0
  queue_fwd(s0, 0, INT_MAX);
  queue_rev(d0, 0, INT_MAX);

  // Maintain fmin = dist[s] - pot[s] (similarly for rmin), so the 
  // path components add up.
  int fmin(-pot[s0]);
  int rmin(pot[d0]);

  bool ret = false;
  while(fmin + rmin <= cap) {
    if(fmin <= rmin) {
      dim_id s(fqueue.removeMin());
      assert(fdist[s] - pot[s] == fmin);
      int s_wt = fdist[s];
      for(act_info e : dims[s].lb_act) {
        // The remaining edges weren't set at the time of inference.
        if(finished.pos(e.c) >= timestamp)
          break;
        if(rseen.elem(e.y)) {
          int wt(s_wt + e.wt + rdist[e.y]);
          if(wt <= cap) {
            // Found a path. Set the rest of fpred.
            dim_id d(e.y);
            fpred[d] = e.c;
            while(d != d0) {
              cst_id c(rpred[d]);   
              fpred[csts[c].y] = c;
              d = csts[c].y;
            }
            ret = true;
            goto path_cleanup;
          }
        } else {
          queue_fwd(e.y, s_wt + e.wt, e.c);
        }
      }
      if(fqueue.empty())
        goto path_cleanup;
      fmin = fdist[fqueue.getMin()] - pot[fqueue.getMin()];
    } else {
      dim_id d(rqueue.removeMin());
      int d_wt = rdist[d];
      assert(d_wt + pot[d] == rmin);
      for(act_info e : dims[d].ub_act) {
        if(finished.pos(e.c) >= timestamp)
          break;
        if(fseen.elem(e.y)) {
          spval_t wt(d_wt + e.wt + fdist[e.y]);
          if(wt <= cap) {
            // Found a solution. Finish filling in fpred.
            fpred[d] = e.c;
            while(d != d0) {
              cst_id c(rpred[d]);   
              fpred[csts[c].y] = c;
              d = csts[c].y;
            }
            ret = true;
            goto path_cleanup;
          }
        } else {
          queue_rev(e.y, d_wt + e.wt, e.c);
        }
      }
      if(rqueue.empty())
        goto path_cleanup;
      rmin = rdist[rqueue.getMin()] + pot[rqueue.getMin()];
    }
  }
  // fprintf(stderr, "%% Length bound: %d ( > %d)\n", fmin + rmin, eff_cap);
path_cleanup:
  fqueue.clear(); fseen.clear();
  rqueue.clear(); rseen.clear();
  // At this point, we've proven the shortest
  // path is has length greater than cap.
  return ret;
#else
  queue_fwd(s0, 0, INT_MAX);
  while(!fqueue.empty()) {
    dim_id s(fqueue.removeMin());
    if(s == d0) {
      fseen.clear(); fqueue.clear();
      return fdist[s] <= cap;
    }
    for(act_edge act : fwd[s]) {
      queue_fwd(act.dim, fdist[s] + act.wt, act.cst_id);
    }
  }
  fseen.clear();
  return false;
#endif
}

auto diff_manager_bv::get_dim(intvar x) -> dim_id {
  auto it(dim_map.find(x.p));
  if(it != dim_map.end())
    return (*it).second;

  // Otherwise, we need to allocate all the helper data.
  dim_id d(vars.size());
  vars.push(x);
  pot.push(0);
  flag.push(0);
  fdist.push(0); fpred.push(INT_MAX); fseen.growTo(d+1);
  rdist.push(0); rpred.push(INT_MAX); rseen.growTo(d+1);

#ifdef LATE_DIFFLOGIC
  stackpred.push(0);
#endif

  fwd.push();
  rev.push();

  int succ_blocks = B32::req_words(d+1);
  if(! (d & B32::block_mask())) { // New block.
    rseen_words = static_cast<int*>(realloc(rseen_words, sizeof(int) * succ_blocks));
    rseen_end = rseen_words;
    rseen_bits = static_cast<uint32_t*>(realloc(rseen_bits, sizeof(uint32_t) * succ_blocks));
    rseen_bits[B32::block(d)] = 0;
  }

  susp_lb.push(new susp_sep); /* susp_lb.last()->growTo(d+1); */
  susp_ub.push(new susp_sep); /* susp_ub.last()->growTo(d+1); */
  susp_succ.push();

  lb_change.growTo(d+1); ub_change.growTo(d+1);

  // All the bookkeeping.

  dim_map.insert(std::make_pair(x.p, d)); 

  x.attach(E_LB, watch<&P::wake_lb>(d));
  x.attach(E_UB, watch<&P::wake_ub>(d));
  return d;
}

auto diff_manager_bv::get_rel(dim_id s, dim_id d) -> rel_id {
  auto it(rel_map.find(std::make_pair(s, d)));
  if(it != rel_map.end())
    return (*it).second;

  //  cst_id zero_cst = csts.size();
  rel_id rel = rels.size();

  csts.push(cst_info(s, d, INT_MAX, at_True, rel));
  rels.push(rel_info {
      INT_MAX,  // wt
      INT_MAX, // sus_wt

      TRUE_CST, // cst

    // Cross-references.
      0, // {fwd,rev}_idx (not yet set)
      0,

      TRUE_CST, // sus_cst

      s, d,

      // lb_idx, ub_idx, sus_block (not set)
      0, 0, 0
      });
  return rel;
}

/*
static pval_t diff_manager_bv::imp_init_bounds(void* ptr, int c_id, ctx_t& ctx) {
  diff_manager_bv* man(static_cast<diff_manager_bv*>(ptr));
  const cst_info& cst(man->csts[c_id]);
  if(vars[cst.s].lb(ctx) - vars[cst.d].ub(ctx) <= cst.wt) {
    return pval_inv(from_int(0));
  }
  return pval_inv(from_int(1));
}

static void diff_manager_bv::imp_ex_bounds(void* ptr, int c_id, pval_t val, vec<clause_elt>& expl) {
  diff_manager_bv* man(static_cast<diff_manager_bv*>(ptr));
  const cst_info& cst(man->csts[c_id]);
  int s_lb = man->vars[cst.s].lb(man->s->ctx());
  EX_PUSH(expl, man->vars[cst.s] < s_lb);
  EX_PUSH(expl, man->vars[cst.d] >= s_lb - cst.wt);
}

static pval_t diff_manager_bv::imp_init_diff(void* ptr, int c_id, ctx_t& ctx) {
  diff_manager_bv* man(static_cast<diff_manager_bv*>(ptr));
  // 
}

static void eqat_ex_ub(void* ptr, int ei, pval_t val, vec<clause_elt>& elts) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  if(pred_lb(ext->s, ext->p) > ext->vals[ei]) {
    elts.push(le_atom(ext->p, ext->vals[ei]));
  } else {
    assert(pred_ub(ext->s, ext->p) < ext->vals[ei]);
    elts.push(ge_atom(ext->p, ext->vals[ei]));
  }
}

static void diff_manager_bv::finalize_bounds(solver_data* s, void* ptr, int ei) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  pid_t x_pi = ext->p;
  pval_t val = ext->vals[ei];
  // patom_t at((*(ext->eqtable.find(val))).second);
  patom_t at(VAL(*(ext->eqtable.find(val))));
  add_clause_(s, at, ~patom_t(x_pi, val), patom_t(x_pi, val+1));
}

static void diff_manager_bv::finalize_diff(solver_data* s, void* ptr, int ei) {
  ivar_ext* ext(static_cast<ivar_ext*>(ptr));
  pid_t x_pi = ext->p;
  pval_t val = ext->vals[ei];

  patom_t at(VAL(*(ext->eqtable.find(val))));
  add_clause_(s, ~at, patom_t(x_pi, val));
  add_clause_(s, ~at, ~patom_t(x_pi, val+1));
}
*/

// From variables with suspended successors, branch
// on the activation variables.
template<int ValC>
struct branch_dim {
  static forceinline int score_rel(solver_data* s, diff_manager_bv* man, int rel) {
    const auto& r(man->rels[rel]);

    switch(ValC) {
    case Val_Min:
      // We'll be enforcing the tightest constraint we can find, so rank by
      // ub(y) + wt.
      return r.wt + man->vars[r.d].ub(s->ctx());
    case Val_Max:
      // Negating the weakest suspended constraint. Because it's half-reif, not exactly
      // the same as forcing rel.s later.
      return -r.wt - man->vars[r.d].lb(s->ctx());
    }
  }

  static forceinline patom_t branch_rel(solver_data* s, diff_manager_bv* man, int rel) {
    int wt = man->rels[rel].wt;
    int cst = man->rels[rel].sus_cst;

    while(man->csts[cst].wt < wt) {
      if(man->csts[cst].act.ub(s->ctx())
         && !man->csts[cst].act.lb(s->ctx()))
        break;
      cst = man->csts[cst].diff_next;
    }
    switch(ValC) {
    case Val_Min:
      return man->csts[cst].act;
    case Val_Max:
      return ~man->csts[cst].act;
    default:
      GEAS_NOT_YET;
      return at_False;
    }
  }

  static forceinline patom_t branch_val(solver_data* s, intvar x) {
    // Not yet fixed.
    assert(x.lb(s->ctx()) < x.ub(s->ctx()));

    switch(ValC) {
    case Val_Min:
      return x <= x.lb(s->ctx());
    case Val_Max:
      return x >= x.ub(s->ctx());
    default:
      GEAS_NOT_YET;
      return at_Error;
    }
  }
};

template<int VarC>
struct branch_score {
  static forceinline int score(solver_data* s, intvar x) {
    switch(VarC) {
    case Var_Smallest:
      return x.lb(s->ctx());
    case Var_Largest:
      return -x.ub(s->ctx());
    case Var_FirstFail:
      return x.ub(s->ctx()) - x.lb(s->ctx());
    default:
      GEAS_NOT_YET;
      return 0;
    }
  }
};

template<int VarC, int ValC>
class diff_order_branch : public geas::brancher {
public:
  diff_order_branch(solver_data* s, vec<intvar>& xs)
    : begin(nullptr) {
    auto man = diff_manager_bv::get(s);
    for(intvar x : xs)
      dims.push(man->get_dim(x));

    begin.x = dims.begin();
  }

  ~diff_order_branch(void) { }

  inline bool rel_has_suspended(solver_data* s, diff_manager_bv* man, int rel) {
    int wt = man->rels[rel].wt;
    int cst = man->rels[rel].sus_cst;

    while(man->csts[cst].wt < wt) {
      if(man->csts[cst].act.ub(s->ctx())
         && !man->csts[cst].act.lb(s->ctx()))
        return true;
      cst = man->csts[cst].diff_next;
    }
    return false;
  }
  /*
  inline bool dim_has_suspended(solver_data* s, diff_manager_bv* man, int dim) {
    if(man->susp_lb[dim]->empty())
      return false;

    const auto& susp_lb(*man->susp_lb[dim]);
    for(int ii = 0; ii < susp_lb.heap.size(); ++ii) {
      if(rel_has_suspended(s, man, susp_lb.rel[susp_lb.heap[ii]]))
        return true;
    }
    return false;
  }
  */
  
  inline int* filter(solver_data* s) {
    auto man = diff_manager_bv::get(s);
    int* dest = begin;
    int* it = begin;
    int* en = dims.end();

    for(; it != en; ++it) {
      if(man->vars[*it].is_fixed(s->ctx())) {
        std::swap(*dest, *it);
        ++dest;
      }
    }
    return dest;
  }

  patom_t branch(solver_data* s) {
    auto man =  diff_manager_bv::get(s);

    // Pick only unfixed variables.
    auto it = filter(s);
    auto end = dims.end();
    if(it == end)
      return at_Undef;

    // Pick the origin dim.
    int sel = *it;
    int sel_lb = branch_score<VarC>::score(s, man->vars[sel]);
    for(++it; it != end; ++it) {
      int curr_lb = branch_score<VarC>::score(s, man->vars[*it]);
      if(curr_lb < sel_lb) {
        curr_lb = sel_lb;
        sel = *it;
      }
    }

    // Now we've picked the origin dim.
    // Branch first on any un-ground orderings.
    susp_sep& s_sep(*man->susp_lb[sel]);

    // Pick the end-point with smallest upper bound.
    int ii = 0;
    for(; ii < s_sep.heap.size(); ++ii) {
      if(rel_has_suspended(s, man, s_sep.rel[s_sep.heap[ii]]))
        goto found_susp_rel;
    }
    // No suspended relation found. Just branch on the domain.
    return branch_dim<ValC>::branch_val(s, man->vars[sel]);

found_susp_rel:
    auto sel_rel = s_sep.rel[s_sep.heap[ii]];
    int sel_score = branch_dim<ValC>::score_rel(s, man, sel_rel);

    for(++ii; ii < s_sep.heap.size(); ++ii) {
      auto rel = s_sep.rel[s_sep.heap[ii]];
      if(!rel_has_suspended(s, man, rel))
        continue;
      int rel_score = branch_dim<ValC>::score_rel(s, man, rel);
      if(rel_score < sel_score) {
        sel_rel = rel;
        sel_score = rel_score;
      }
    }
    return branch_dim<ValC>::branch_rel(s, man, sel_rel);
  }
  
  bool is_fixed(solver_data* s) {
    filter(s);
    return begin < dims.end();
  }

  vec<int> dims;
  trailed<int*> begin;
};
  
void diff_manager_bv::report_internal(void) {
#ifdef REPORT_INTERNAL_STATS
  fprintf(stderr, "%% DIFF-BV(%d) : %d executions, %d lb, %d ub, %d bnd, %d diff\n",
          prop_id,
          exec_count,
          lb_count,
          ub_count,
          bnd_count,
          diff_count);
#endif
}
namespace geas {
namespace difflogic {

bool post_bv(solver_data* s, patom_t r, intvar x, intvar y, int k) {
  diff_manager_bv* man(diff_manager_bv::get(s));  
  return man->post(r, x, y, k);
}

template<int VarC>
brancher* _branch_order(solver_data* s, ValChoice valc, vec<intvar>& xs) {
  switch(valc) {
  case Val_Min:
    return new diff_order_branch<VarC, Val_Min>(s, xs);
  case Val_Max:
    return new diff_order_branch<VarC, Val_Max>(s, xs);
  default:
    GEAS_NOT_YET;
    return nullptr;
  }
}

brancher* branch_order(solver_data* s, VarChoice varc, ValChoice valc, vec<intvar>& xs) {
  // diff_manager_bv* man(diff_manager_bv::get(s));  
  switch(varc) {
  case Var_Smallest:
    return _branch_order<Var_Smallest>(s, valc, xs);
  case Var_Largest:
    return _branch_order<Var_Largest>(s, valc, xs);
  case Var_FirstFail:
    return _branch_order<Var_FirstFail>(s, valc, xs);
  default:
    GEAS_NOT_YET;
    return nullptr;
  }
  //  brancher* b = new diff_order_branch(s, xs);
}

}
}
