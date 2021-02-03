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
    //int operator[](int idx) const { return xref[idx]; }
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
  /*
  struct rel_info {
    // Cross-references into fwd and rev, for when we
    // activate new constraints.
    int s_act_idx;
    int d_act_idx;
  };
  */
  
  // Information about suspended differences
  /*
  struct diff_info {
    static diff_info no_cst(void) {
      diff_info diff = {
        INT_MAX,
        INT_MAX,
        TRUE_CST,

        0, 0, // fwd/rev crossreferences
        TRUE_CST
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
  };
  */

  // Information about suspended differences
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

  //=====================
  // Persistence management
  //=====================
  vec<susp_trail_entry> susp_trail;
  Tuint susp_trail_sz;
  
  // inline diff_info& get_info(int s, int d) { return diffs[s][d]; }

  struct rel_tag {
    rel_tag(void) : s(0), d(0) { }
    rel_tag(dim_id _s, dim_id _d)
      : s(_s), d(_d) { assert(s < 1<<16); assert(d < 1<<16); }

    unsigned s : 16;
    unsigned d : 16;
  };
  /*
  inline unsigned rel_id(dim_id s, dim_id d) {
    return cast::conv<unsigned>(rel_tag(s, d));
  }
  */

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

  /*
    struct eval_lb_wit {
    int operator()(cst_id c) const {
    if(d->finished.elem(c))
    return INT_MAX;
    return d->csts[c].wit;
    }
    diff_manager_bv* d;
    };
    struct eval_ub_wit {
    int operator()(cst_id c) const {
    if(d->finished.elem(c))
    return INT_MAX;
    return -(d->csts[c].wit - d->csts[c].wt);
    }
    diff_manager_bv* d;
    };
  */

  /*
    void check_potential(void) {
    for(dim_id d : irange(dims.size())) {
    for(act_info act : dims[d].lb_act) {
    assert(pot[d] + act.wt - pot[act.y] >= 0);
    }
    }
    }
    void check_witnesses(void) {
    for(unsigned int ci : finished.complement()) {
    assert(lb(vars[csts[ci].x]) <= csts[ci].wit);
    assert(csts[ci].wit <= ub(vars[csts[ci].y]) + csts[ci].wt);
    assert(dims[csts[ci].x].threshold_lb.root_val() <= csts[ci].wit);
    assert(dims[csts[ci].y].threshold_ub.root_val() <= -(csts[ci].wit - csts[ci].wt));
    }
    }
  */


  // Can't use finished.elem directly, because
  // we haven't yet untrailed.
  /*
  inline bool is_finished(cst_id c) {
    return finished.pos(c) < finished_sz;
  }
  */

  watch_result wake_r(int ci) {
    /*
      if(!is_finished(activators[ri].c)) {
      act_queue.push(ri);
      queue_prop();
      }
    */
    // TODO
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
    /*
      untrail();
    */
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
    // dim_id v0(vars.size());

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

  bool process_killed(cst_id c, vec<clause_elt>& confl);
  bool propagate_if_killed(cst_id c, cst_id e, vec<clause_elt>& confl);
  
  void untrail(void);
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
  //  vec<dim_info> dims;

  // vec<diff_info> csts; 
  // p_sparseset finished;
  // Tuint finished_sz;

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
        uint32_t d_bit = B32::bit(dy);
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

  // Need to fill rdist first, everything
  // always looks redundant.
  rpred[cst.s] = ci;
  fill_rdist(cst.s, cst.d, cst.wt);
  if(rseen_vars.size() == 0) {
    rseen_vars.clear();
    return true;
  }
  fpred[cst.d] = ci;
  fill_fdist(cst.s, cst.d, cst.wt);
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
  /*
  if(rseen_vars.size() == 0) {
    rseen_vars.clear();
    return true;
  }
  */

  // Set up the bitmap for process_suspended.
  for(int v : rseen_vars)
    bv_insert(rseen_end, rseen_bits, v);
  bool okay = process_suspended(cst.wt)
    && process_act_bounds(cst.s, cst.d);

  // Clear transient state
  bv_clear(rseen_words, rseen_end, rseen_bits);
  rseen_vars.clear();
  fseen_vars.clear();

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
  /*
    uint64_t* succs(susp_succ[s]);

    for(int r_w : range(rseen_words, rseen_end)) {
      if(succs[r_w] & rseen_bits[r_w]) {
        int base = r_w << B64::block_bits();
        uint64_t word = succs[r_w] & rseen_bits[r_w];
        bool okay = B64::Forall_Word(base, word, [this, s, delta](int d) {
            return process_suspended_rel(s, d, delta);
          });
        if(!okay) {
          bv_clear(rseen_words, rseen_end, rseen_bits);
          return false;
        }
      }
    }
  */
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
      if(!set_lb(vars[act.dim], s_lb - act.wt,
                 expl<&P::ex_lb>(act.cst_id)))
        return false;
      if(!process_lb_change(act.dim))
        return false;
    }
  }

  // Now check the suspended constraints.
  auto& s_susp(*susp_lb[s]);
  while(!s_susp.heap.empty()) {
    int rel_idx = s_susp.heap.getMin();
    rel_id rel = s_susp.rel[rel_idx];
    rel_info& diff(rels[rel]);
    int d = diff.d;

    if(s_lb <= s_susp.sep[rel_idx])
      break;

    int d_ub = ub(vars[d]);
    int diff_min = s_lb - d_ub;
    //    diff_info& diff(get_info(s, d));
    int sus_wt = diff.sus_wt;
    int sus_cst = diff.sus_cst;
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

      if(diff.wt <= sus_wt) {
        // Remaining suspended constraints are redundant.
        s_susp.heap.removeMin();
        susp_ub[d]->heap.remove(diff.ub_idx);
        susp_succ[s][diff.susp_block].mask &= ~B32::bit(d);
        continue;
      }
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
      if(!set_ub(vars[act.dim], d_ub + act.wt,
                 expl<&P::ex_ub>(act.cst_id)))
        return false;
      if(!process_ub_change(act.dim))
        return false;
    }
  }

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

      if(diff.wt <= sus_wt) {
        // Remaining suspended constraints are redundant.
        d_susp.heap.removeMin();
        susp_lb[s]->heap.remove(diff.lb_idx);
        susp_succ[s][diff.susp_block].mask &= ~B32::bit(d);
        continue;
      }
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
void diff_manager_bv::untrail(void) { untrail_to(susp_trail_sz); }
                                        
// ===========
// Explanation
// ===========
void diff_manager_bv::ex_lb(int ci, pval_t p, vec<clause_elt>& expl) {
  //rel_tag tag(cast::conv<rel_tag>(ci));
  // const diff_info& diff(get_info(tag.s, tag.d));
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

  fwd.push();
  rev.push();

  /*
  diffs.push();
  for(dim_id ii = 0; ii < d; ++ii) {
    diffs[ii].push(diff_info::no_cst());
    susp_lb[ii]->growTo(d+1);
    susp_ub[ii]->growTo(d+1);
  }
  diffs.last().growTo(d+1, diff_info::no_cst());
  */

  int succ_blocks = B32::req_words(d+1);
  if(! (d & B32::block_mask())) { // New block.
    /*
    for(dim_id ii = 0; ii < d; ++ii) {
      // FIXME: check for allocation errors
      susp_succ[ii] = static_cast<uint64_t*>(realloc(susp_succ[ii], sizeof(uint64_t) * succ_blocks));
      susp_succ[ii][B64::block(d)] = 0;
    }
    */
    rseen_words = static_cast<int*>(realloc(rseen_words, sizeof(int) * succ_blocks));
    rseen_end = rseen_words;
    rseen_bits = static_cast<uint32_t*>(realloc(rseen_bits, sizeof(uint32_t) * succ_blocks));
    rseen_bits[B32::block(d)] = 0;
  }
  // susp_succ.push(static_cast<uint64_t*>(calloc(succ_blocks, sizeof(uint64_t))));

  susp_lb.push(new susp_sep); /* susp_lb.last()->growTo(d+1); */
  susp_ub.push(new susp_sep); /* susp_ub.last()->growTo(d+1); */
  susp_succ.push();

  /*
  dims.push(dim_info(this));
  */
  lb_change.growTo(d+1); ub_change.growTo(d+1);
  // lb_check.growTo(d+1); ub_check.growTo(d+1);
  // GEAS_NOT_YET;

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

}
}
