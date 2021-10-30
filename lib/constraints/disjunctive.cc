#include <climits>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>

// #include <geas/utils/ps-tree.h>
#include <geas/constraints/disjunctive-impl.hh>

#include <geas/solver/solver.h>
#include <geas/constraints/builtins.h>
// What's the easiest way to factor this out, so we propagate LCT
// as well (without unnecessary overhead)?

namespace geas {

struct ef_data {
  static ef_data nil(void) { return ef_data(0, INT_MIN, 0, INT_MIN); }
  static ef_data smudged(int est, int dur) { return ef_data(0, INT_MIN, dur, est+dur); }
  static ef_data task(int est, int dur) { return ef_data(dur, est+dur, dur, est+dur); }

  ef_data(void) : d_sum(0), ect(INT_MIN), o_sum(0), o_ect(INT_MIN) { }
  ef_data(int _d_sum, int _ect, int _o_sum, int _o_ect) : d_sum(_d_sum), ect(_ect), o_sum(_o_sum), o_ect(_o_ect) { }
  int d_sum;
  int ect;
  int o_sum;
  int o_ect;
};

void ef_smudge(ef_data& leaf) {
  // These *should* already be set.
  leaf.o_sum = leaf.d_sum;
  leaf.o_ect = leaf.ect;

  leaf.d_sum = 0;
  leaf.ect = INT_MIN;
}
void ef_remove(ef_data& leaf) {
  leaf.o_sum = 0;
  leaf.o_ect = INT_MIN;
  leaf.d_sum = 0;
  leaf.ect = INT_MIN;
}

inline void ol_merge(ef_data l, ef_data r, ef_data& out) {
  out.d_sum = l.d_sum + r.d_sum;
  out.ect = std::max(l.ect + r.d_sum, r.ect);
}

 
inline void ef_merge(ef_data l, ef_data r, ef_data& out) {
  out.d_sum = l.d_sum + r.d_sum;
  out.ect = std::max(l.ect + r.d_sum, r.ect);

  out.o_sum = std::max(l.o_sum + r.d_sum, l.d_sum + r.o_sum);
  out.o_ect = std::max(std::max(l.o_ect + r.d_sum,
                                l.ect + r.o_sum),
                       r.o_ect);
}

// Navigating nodes
static inline int _left(int n) { return (n << 1) + 1; }
static inline int _right(int n) { return (n << 1) + 2; }
static inline int _parent(int n) { return (n-1)>>1; }

template<void (*Op)(ef_data, ef_data, ef_data&)>
struct ef_op {
  // Assumes all the leaf nodes are set.
  template<class It>
  static void /* __attribute__((noinline)) */ rebuild(It nodes, int base) {
    for(int ii = base-1; ii >= 0; --ii) {
      Op(nodes[_left(ii)], nodes[_right(ii)], nodes[ii]);
    }
  }

  // Could make this a little lazier, since we're
  // always re-loading both.
  template<class It>
  static void /*__attribute__((noinline))*/ update(It nodes, int base, int idx) {
    int p = base + idx;
    while(p > 0) {
      p = _parent(p);
      Op(nodes[_left(p)], nodes[_right(p)], nodes[p]);
    }
  }

  // Should already have been smudged
  template<class It>
  static void ef_remove(It nodes, int base, int idx) {
    int p = base + idx;

  }
};

int dp_effective_ect(ef_data* nodes, int sz, int idx) {
  int p = sz + idx;
  int ect = INT_MIN;
  int sum = 0;

  while(p > 0) {
    if(p & 1) { // Left child
      ect = std::max(ect + nodes[p+1].d_sum, nodes[p+1].ect);
      sum += nodes[p+1].d_sum;
    } else { // Right child
      ect = std::max(nodes[p-1].ect + sum, ect);
      sum += nodes[p-1].d_sum;
    }
    p = _parent(p);
  }
  return ect;
}

// For detectable precedences, identify the start of the envelope.
int ect_binding_task(int ex_ect, ef_data* nodes, int sz) {
  int p = 0;
  while(p < sz) {
    const ef_data& rt = nodes[_right(p)];
    // If the right subtree is enough to push
    // up the ECT, use that.
    if(rt.ect >= ex_ect) {
      p = _right(p);
    } else {
      // Otherwise, take the left subtree,
      // accounting for the sum of the right.
      ex_ect -= rt.d_sum;
      p = _left(p);
    }
  }

  return p - sz;
}

// Check which smudged task would cause an overload.
int ef_blocked_task(int ex_ect, ef_data* nodes, int sz) {
  // Prefer rightmost tasks for now.
  int p = 0;

  while(p < sz) {
    // Couple of cases.
    const ef_data& l(nodes[_left(p)]);
    const ef_data& r(nodes[_right(p)]);

    // Check whether one of the
    // subtrees is sufficient.
    if(r.o_ect > ex_ect) {
      p = _right(p);
      continue;
    }
    if(l.o_ect > ex_ect) {
      p = _left(p);
      continue;
    }
    if(l.ect + r.o_sum > ex_ect) {
      // Switch to explaining the sum.
      ex_ect -= l.ect;
      p = _right(p);
      break;
    }
    // Should be the final case.
    assert(l.o_ect + r.d_sum > ex_ect);
    ex_ect -= r.d_sum;
    p = _left(p);
  }

  // At this point, we've switched to explaining the sum.
  while(p < sz) {
    const ef_data& l(nodes[_left(p)]);
    const ef_data& r(nodes[_right(p)]);
    if(l.d_sum + r.o_sum > ex_ect) {
      ex_ect -= l.d_sum;
      p = _right(p);
    } else {
      ex_ect -= r.d_sum;
      p = _left(p);
    }
  }
  return p - sz;
}

// Find the leftmost relevant task in the envelope identified
// by edge-finding.
int ef_binding_task(int ex_ect, const ef_data* nodes, int sz) {
  // Prefer rightmost tasks for now, because we're just using it
  // to detect the extent of the envelope.
  int p = 0;

  while(p < sz) {
    // Couple of cases.
    const ef_data& l(nodes[_left(p)]);
    const ef_data& r(nodes[_right(p)]);
    // Check whether we can get away
    // with just the right subtree.
    if(r.o_ect >= ex_ect) {
      p = _right(p);
      continue;
    }
    if(l.ect + r.o_sum >= ex_ect) {
      // Now we consider only the ect and d_sum.
      ex_ect -= r.o_sum;
      p = _left(p);
      break;
    }
    // Should be the final case.
    assert(l.o_ect + r.d_sum >= ex_ect);
    ex_ect -= r.d_sum;
    p = _left(p);
  }

  // At this point, we're either done, or explaining the
  // (definite) ect.
  while(p < sz) {
    const ef_data& l(nodes[_left(p)]);
    const ef_data& r(nodes[_right(p)]);
    if(r.ect >= ex_ect) {
      p = _right(p);
    } else {
      ex_ect -= r.d_sum;
      p = _left(p);
    }
  }
  return p - sz;
}

// Assuming task is a smudged task, find the time it
// will be pushed up to.
std::pair<int, int> ef_effective_env(int task, ef_data* nodes, int sz) {
  int p = task+sz;

  int left_node = p;

  int o_sum = nodes[p].o_sum;
  int o_ect = nodes[p].o_ect;
  int d_sum = 0;

  int env_sum = 0;

  while(p > 0) {
    // Walk upwards, doing something?
    if(p & 1) {
      // Current node was a left child,
      // just add the nodes to the right.
      int d_right = nodes[p+1].d_sum;
      o_sum += d_right;
      o_ect += d_right;
      d_sum += d_right;
      env_sum += d_right;
    } else {
      // Was a right child. Check if the left child
      // pushes up the ect.
      if(nodes[p-1].ect + o_sum > o_ect) {
        left_node = p-1;
        o_ect = nodes[p-1].ect + o_sum;
        env_sum = d_sum;
      }
      int d_left = nodes[p-1].d_sum;
      o_sum += d_left;
      d_sum += d_left;
    }
    p = _parent(p);
  }
  int env_ect = nodes[left_node].ect + env_sum;

  // Now walk back down the left subtree to find
  // the binding task.
  p = left_node;
  while(p < sz) {
    const ef_data& l(nodes[_left(p)]);
    const ef_data& r(nodes[_right(p)]);
    if(l.ect + r.d_sum > r.ect) {
      p = _left(p);
    } else {
      p = _right(p);
    }
  }
  return std::make_pair(p - sz, env_ect);
}

class disjunctive : public propagator, public prop_inst<disjunctive> {
  enum Flags { Dis_EF = 1, Dis_DP = 2, Dis_ALL = 3 };

  static inline unsigned HIGH(unsigned tag) { return tag >> 16; }
  static inline unsigned LOW(unsigned tag) { return tag & ((1 << 16)-1); }
  static inline unsigned TAG(unsigned high, unsigned low) { return (high << 16) | low; }

  watch_result wake(int xi) {
    queue_prop();
    return Wt_Keep;
  }
  
  // Explanation functions
  bool check_sat(ctx_t& ctx);
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  public:
    // We need to pad nodes to the given
    static int nodes_base(int sz) { return (1 << (32 - __builtin_clzll(sz-1)))-1; }
  disjunctive(solver_data* s, vec<intvar>& _st, vec<int>& _du, unsigned _prop_flag = /*Dis_EF */ Dis_ALL)
      : propagator(s)
      , sz(_st.size())
      , base(nodes_base(sz))
      , start(new intvar[sz]), du(new int[sz])

      , est(new int[sz])
      , lct(new int[sz])

      , p_est(new int[sz])
      , p_lct(new int[sz])
      , index_of(new int[sz])
        
      , ect_tree(new ef_data[2 * base + 1])

      , ex_buf(new int[sz])
      , ex_sz(0)
        
      , prop_mode(_prop_flag)
  {
    assert(prop_mode);
    for(int ii : irange(_st.size())) {
      intvar x = _st[ii];
      start[ii] = x; x.attach(E_LU, watch<&P::wake>(ii));
      du[ii] = _du[ii];
      p_est[ii] = p_lct[ii] = index_of[ii] = ii;
    }
    for(int ii = base + sz; ii < 2*base + 1; ++ii)
      ect_tree[ii] = ef_data::nil();
  }

  ~disjunctive(void) {
    delete[] start;
    delete[] du;
    delete[] est;
    delete[] lct;
    delete[] p_est;
    delete[] p_lct;
    delete[] ect_tree;
    delete[] ex_buf;
  }

    void cleanup(void) {
      is_queued = false;
    }

    void root_simplify(void) {
      return; 
    }

  // These assume the 'est' array has been
  // filled appropriately.
  inline bool set_est_ef(int ti, int est, int tag) {
    return set_lb(start[ti], est, expl<&P::ex_lb_ef>(tag, expl_thunk::Ex_BTPRED));
  }
  inline bool set_lst_ef(int ti, int est, int tag) {
    return set_ub(start[ti], -est-du[ti], expl<&P::ex_ub_ef>(tag, expl_thunk::Ex_BTPRED));
  }
  inline bool set_est_dp(int ti, int est) {
    return set_lb(start[ti], est, expl<&P::ex_lb_dp>(ti, expl_thunk::Ex_BTPRED));
  }
  inline bool set_lst_dp(int ti, int est) {
    return set_ub(start[ti], -est-du[ti], expl<&P::ex_ub_dp>(ti, expl_thunk::Ex_BTPRED));
  }

  template<class F>
  bool prop_edgefind(void);
  template<class F>
  bool prop_det_prec(void);

  bool propagate_est(vec<clause_elt>& confl);
  bool propagate_lct(vec<clause_elt>& confl);

  void ex_lb_ef(int tag, pval_t p, vec<clause_elt>& expl);
  void ex_lb_dp(int tag, pval_t p, vec<clause_elt>& expl);
  void ex_ub_ef(int tag, pval_t p, vec<clause_elt>& expl);
  void ex_ub_dp(int tag, pval_t p, vec<clause_elt>& expl);

  void ex_dp(int ex_task, int ex_lb);
  void ex_ef(int ex_task, int ex_lb, int env_lb);
  void ex_overload(int ect);

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running disjunctive]]" << std::endl;
#endif
      // Not idempotent, probably better to loop
      // until fixpoint.
      changed = true;
      while(changed) {
        changed = false;
        if(!propagate_est(confl))
          return false;
        if(!propagate_lct(confl))
          return false;
      }
      return true;
    }

  void dump_schedule(void);

  // Putting this here for now.
  void detect_precedences(void);
  
  // Parameters
  int sz;
  int base;
  intvar* start;
  int* du;

  char prop_mode;
  
  // Transient storage (re-used for lct)
  int* est;
  int* lct;

  // Temporary storage
  int* p_est;
  int* p_lct;
  int* index_of;

  ef_data* ect_tree;

  // Track whether we've reached a fixpoint.
  bool changed;
  
  // For collecting explanations
  int* ex_buf;
  int ex_sz;
  int env_l;
  int env_u;

  struct ex_info {
    ex_info(int _t_ex, int _env_lb)
      : t_ex(_t_ex), env_lb(_env_lb) { }
    int t_ex;
    int env_lb;
  };
  vec<ex_info> exs;

  int mk_expl(int t_ex, int env_lb) {
    int id = exs.size();
    trail_push(s->persist, exs._size());
    exs.push(ex_info(t_ex, env_lb));
    return id;
  }
};

void disjunctive::detect_precedences(void) {
  // Earliest *completion* time.
  std::sort(p_est, p_est + sz,
            [this](int t, int u) { return est[t] + du[t] < est[u] + du[u]; });

  // Latest *start* time.
  std::sort(p_lct, p_lct + sz,
            [this](int t, int u) { return lct[t] - du[t] < lct[u] - du[u]; });

  // Basically same machinery as detectable precedences, but collecting the
  // (reduced) set of implications, instead of computing envelopes.
  p_sparseset before(sz);
  vec< vec<int> > preds(sz);

  auto p_it = p_est;
  auto p_en = p_est+sz;

  for(int t : range(p_lct, p_lct+sz)) {
    for(int gp : preds[t])
      before.remove(gp);
    before.insert(t);

    for(; p_it != p_en; ++p_it) {
      int succ = *p_it;
      if(lct[t] - du[t] >= est[succ] + du[succ])
        break;
      // Successor.
      for(int p : before)
        preds[succ].push(p);
    }
  }
  fprintf(stderr, "%% Preds: [");
  for(int t : irange(sz)) {
    for(int p : preds[t])
      fprintf(stderr, "%d < %d,", p, t);
  }
  fprintf(stderr, "]\n");
}

// *The Business*: 
// For task t, we want the set of other tasks which
// must _start_ before t can _finish_.
template<class F>
bool disjunctive::prop_det_prec(void) {
  std::sort(p_est, p_est + sz,
            [this](int t, int u) { return est[t] < est[u]; });

  // Actually by *decreasing* lst.
  std::sort(p_lct, p_lct + sz,
            [this](int t, int u) { return lct[t] - du[t] > lct[u] - du[u]; });

  // Start with everything
  for(int ii = 0; ii < sz; ++ii) {
    int t = p_est[ii];
    index_of[t] = ii;
    ect_tree[base + ii] = ef_data::task(est[t], du[t]);
  }
  ef_op<ol_merge>::rebuild(ect_tree, base);

  auto b_it = p_lct;
  auto b_en = p_lct + sz;

  // Now we're re-sorting *yet again*, this time by decreasing
  // ect.
  std::sort(p_est, p_est + sz,
            [this](int t, int u) { return est[t] + du[t] > est[u] + du[u]; });
  for(int t : range(p_est, p_est + sz)) {
    // Detectable precedence if lst(b) < ect(t).
    int ect_t = est[t] + du[t];
    for(; b_it != b_en; ++b_it) {
      // Remove any tasks which *aren't* definitely
      // before t.
      int lst_b = lct[*b_it] - du[*b_it];
      if(lst_b < ect_t)
        break;
      int idx = index_of[*b_it];
      ect_tree[base + idx] = ef_data::nil();
      ef_op<ol_merge>::update(ect_tree, base, idx);
    }

    int est_t = est[t];
    int prec_ect = dp_effective_ect(ect_tree, base, index_of[t]);
    if(prec_ect > est_t) {
      changed = true;
      if(!F::set_est_dp(this, t, prec_ect))
        return false;
    }
  }
  return true;
}


template<class F>
bool disjunctive::prop_edgefind(void) {
  assert(ex_sz == 0);
  std::sort(p_est, p_est + sz,
            [this](int t, int u) { return est[t] < est[u]; });
  std::sort(p_lct, p_lct + sz,
            [this](int t, int u) { return lct[t] > lct[u]; });
  // Again, start with everything.
  for(int ii = 0; ii < sz; ++ii) {
    int t = p_est[ii];
    index_of[t] = ii;
    ect_tree[base + ii] = ef_data::task(est[t], du[t]);
  }
  ef_op<ef_merge>::rebuild(ect_tree, base);

  // Process by decreasing LCT.
  for(int t : range(p_lct, p_lct + sz)) {
    int t_lct = lct[t]; // The latest LCT still in the tree.
    // Check for overload
    if(ect_tree[0].ect > t_lct) {
      // Explain the overload -- guess we want the minimum
      // set of tasks causing overload?
      // int binding_idx = env_binding_task(ect_tree, t_lct+1, sz);
      ex_overload(t_lct);
      return false;
    }
    while(ect_tree[0].o_ect > t_lct) {
      int o_ect = ect_tree[0].o_ect;
      // A single integrated call, to make sure we get consistent values
      // for the envelope's beginning, duration and the updated task.
      int to_shift = ef_blocked_task(t_lct, ect_tree, base);
      auto env_info = ef_effective_env(to_shift, ect_tree, base);
      int t = p_est[to_shift];
      int env_ect = env_info.second;
      if(est[t] < env_ect) {
        changed = true;
        int env_lb = est[p_est[env_info.first]];
        if(!F::set_est_ef(this, t, env_ect, mk_expl(t, env_lb)))
            return false;
      }
      ect_tree[base + to_shift] = ef_data::nil();
      ef_op<ef_merge>::update(ect_tree, base, to_shift);
    }

    // Make the current task optional.
    int idx = index_of[t];
    ef_smudge(ect_tree[base + idx]);
    ef_op<ef_merge>::update(ect_tree, base, idx);
  }
  return true;
}

// 
void disjunctive::ex_dp(int ex_task, int ex_lb) {
  assert(ex_sz == 0);

  // Collect tasks detectably before ex_task
  int* env_end = p_est;
  int t_ect = est[ex_task] + du[ex_task];
  for(int ii = 0; ii < sz; ++ii) {
    int t = p_est[ii];
    if(t == ex_task)
      continue;
    // Is lst(t) < ect(ex_task).
    if(lct[t] - du[t] < t_ect) {
      p_est[ii] = *env_end;
      *env_end++ = t;
    }
  }

  // Process tasks by *decreasing* est.
  auto cmp = [this](int i, int j) { return est[i] > est[j]; };
  ImpHeap::heapify(cmp, p_est, env_end);

  assert(p_est < env_end);
  int t0 = ImpHeap::pop(cmp, p_est, env_end);
  ex_buf[ex_sz++] = t0;

  int env_begin = est[t0];
  int env_sum = du[t0];

  int env_lct = lct[t0];
  
  while(env_begin + env_sum < ex_lb) {
    assert(p_est < env_end);
    int t = ImpHeap::pop(cmp, p_est, env_end);
    ex_buf[ex_sz++] = t;

    env_begin = est[t];
    env_sum += du[t];
    env_lct = std::max(env_lct, lct[t]);
  }

  // At this point, we have a set O of tasks such that
  // O << ex_task, and ect(O) >= ex_lb.
  env_l = env_begin;
  // Some flex in the choice of upper bound -- anywhere
  // between the maximum lst in the env, and the ect of t.
  // We choose to relax the bound on t, 
  env_u = env_lct;
}

void disjunctive::ex_ef(int ex_task, int ex_lb, int env_begin) {
  assert(ex_sz == 0);

  int* env_end = p_est;
  // Filter tasks with est >= env_begin.
  int t_ect = est[ex_task] + du[ex_task];
  for(int ii = 0; ii < sz; ++ii) {
    int t = p_est[ii];
    // if(lct[t] < t_ect) {
    if(est[t] >= env_begin) {
      p_est[ii] = *env_end;
      *env_end++ = t;
    }
  }

  // Filter tasks which fit in the envelope.
  // We're hoping that most tasks are irrelevant, so
  // we don't do a full sort.
  auto cmp = [this](int t, int u) { return lct[t] < lct[u]; };
  ImpHeap::heapify(cmp, p_est, env_end);
  // Now process tasks. We need to find an envelope which is
  // over-filled, and pushes lb(x) high enough.

  int t0 = ImpHeap::pop(cmp, p_est, env_end);
  ex_buf[ex_sz++] = t0;
  int env_ect = env_begin + du[t0];
  int env_ub = lct[t0];

  // Make sure we collect enough to push up lb(x).
  while(env_ect < ex_lb) {
    assert(p_est != env_end);
    int t = ImpHeap::pop(cmp, p_est, env_end);
    env_ect += du[t];
    env_ub = lct[t];
    ex_buf[ex_sz++] = t;
  }
  // And now make sure the env is an overload.
  env_ect += du[ex_task];
  while(env_ect <= env_ub) {
    assert(p_est != env_end);
    int t = ImpHeap::pop(cmp, p_est, env_end);
    env_ect += du[t];
    env_ub = lct[t];
    ex_buf[ex_sz++] = t;
  }
  env_l = env_begin;
  env_u = env_ub;
}

void disjunctive::ex_overload(int env_lct) {
  assert(ex_sz == 0);

  int* env_end = p_est;
  // Filter tasks with lct <= env_lct.
  for(int ii = 0; ii < sz; ++ii) {
    int t = p_est[ii];
    if(lct[t] <= env_lct) {
      p_est[ii] = *env_end;
      *env_end++ = t;
    }
  }
  // Sort by decreasing est.
  auto cmp = [this](int t, int u) { return est[t] > est[u]; };
  ImpHeap::heapify(cmp, p_est, env_end);

  int t0 = ImpHeap::pop(cmp, p_est, env_end);
  ex_buf[ex_sz++] = t0;
  int env_begin = est[t0];
  int env_sum = du[t0];

  while(env_begin + env_sum <= env_lct) {
    int t = ImpHeap::pop(cmp, p_est, env_end);
    ex_buf[ex_sz++] = t;
    env_begin = est[t];
    env_sum += du[t];
  }
  env_l = env_begin;
  env_u = env_begin + env_sum - 1;
}

struct set_est {
  inline static bool set_est_ef(disjunctive* d, int t, int est, int tag) {
    return d->set_est_ef(t, est, tag);
  }
  inline static bool set_est_dp(disjunctive* d, int t, int est) {
    return d->set_est_dp(t, est);
  }
};
struct set_lct {
  inline static bool set_est_ef(disjunctive* d, int t, int est, int tag) {
    return d->set_lst_ef(t, est, tag);
  }
  inline static bool set_est_dp(disjunctive* d, int t, int est) {
    return d->set_lst_dp(t, est);
  }
};

bool disjunctive::propagate_est(vec<clause_elt>& confl) {
  for(int ii = 0; ii < sz; ++ii) {
    est[ii] = lb(start[ii]);
    lct[ii] = ub(start[ii]) + du[ii];
  }

  if(prop_mode & Dis_DP) {
    //dump_schedule();
    //detect_precedences();
    if(!prop_det_prec<set_est>())
      return false;
  }

  if(prop_mode & Dis_EF) {
    if(!prop_edgefind<set_est>()) {
      if(ex_sz) { // We had an overload.
        for(int t : range(ex_buf, ex_buf + ex_sz)) {
          EX_PUSH(confl, start[t] < env_l);
          EX_PUSH(confl, start[t] > env_u - du[t]);
        }
        ex_sz = 0;
      }
      return false;
    }
  }
  return true;
}

bool disjunctive::propagate_lct(vec<clause_elt>& confl) {
  for(int ii = 0; ii < sz; ++ii) {
    est[ii] = -ub(start[ii]) - du[ii];
    lct[ii] = -lb(start[ii]);
  }

  if(prop_mode & Dis_DP) {
    if(!prop_det_prec<set_lct>())
      return false;
  }

  if(prop_mode & Dis_EF) {
    if(!prop_edgefind<set_lct>()) {
      if(ex_sz) {
        for(int t : range(ex_buf, ex_buf + ex_sz)) {
          EX_PUSH(confl, start[t] < -env_u);
          EX_PUSH(confl, start[t] > -env_l - du[t]);
        }
        ex_sz = 0;
      }
      return false;
    }
  }
  return true;
}

void disjunctive::ex_lb_ef(int tag, pval_t p, vec<clause_elt>& expl) {
  // Set up the data structures
  for(int ii : irange(sz)) {
    est[ii] = lb(start[ii]);
    lct[ii] = ub(start[ii]) + du[ii];
  }
  //int ex_task = HIGH(tag);
  //int env_begin = est[LOW(tag)];
  const ex_info& e(exs[tag]);
  int ex_task = e.t_ex;
  int env_begin = e.env_lb;

  ex_ef(ex_task, start[ex_task].lb_of_pval(p), env_begin);

  // Now reconstruct the explanation.
  EX_PUSH(expl, start[ex_task] < env_l);
  // EX_PUSH(expl, start[ex_task] < lb(start[ex_task]));
  for(int t : range(ex_buf, ex_buf + ex_sz)) {
    EX_PUSH(expl, start[t] < env_l);
    EX_PUSH(expl, start[t] > env_u - du[t]);
    //EX_PUSH(expl, start[t] < lb(start[t]));
    //EX_PUSH(expl, start[t] > ub(start[t]));
  }
  ex_sz = 0;
}

void disjunctive::ex_ub_ef(int tag, pval_t p, vec<clause_elt>& expl) {
  // Set up the data structures
  for(int ii : irange(sz)) {
    est[ii] = -ub(start[ii]) - du[ii];
    lct[ii] = -lb(start[ii]);
  }
  //int ex_task = HIGH(tag);
  //int env_begin = -LOW(tag);
  const ex_info& e(exs[tag]);
  int ex_task = e.t_ex;
  int env_begin = e.env_lb;
  ex_ef(ex_task, -start[ex_task].ub_of_pval(p) - du[ex_task], env_begin);

  // Now reconstruct the explanation.
  EX_PUSH(expl, start[ex_task] > -env_l - du[ex_task]);
  //EX_PUSH(expl, start[ex_task] > ub(start[ex_task]));
  for(int t : range(ex_buf, ex_buf + ex_sz)) {
    EX_PUSH(expl, start[t] < -env_u);
    EX_PUSH(expl, start[t] > -env_l - du[t]);
    //EX_PUSH(expl, start[t] < lb(start[t]));
    //EX_PUSH(expl, start[t] > ub(start[t]));
  }
  ex_sz = 0;
}

void disjunctive::ex_lb_dp(int ex_task, pval_t p, vec<clause_elt>& expl) {
  // Set up the data structures
  for(int ii : irange(sz)) {
    est[ii] = lb(start[ii]);
    lct[ii] = ub(start[ii]) + du[ii];
  }
  ex_dp(ex_task, start[ex_task].lb_of_pval(p));
  int ex_ect = est[ex_task] + du[ex_task];
  int eff_lst = INT_MIN;
  for(int t : range(ex_buf, ex_buf + ex_sz)) {
    // Tighten the envelope for this task, if env_u
    // would allow it to finish before ex_task.
    int t_ub = std::min(env_u - du[t], ex_ect-1);
    EX_PUSH(expl, start[t] < env_l);
    EX_PUSH(expl, start[t] > t_ub);
    //EX_PUSH(expl, start[t] < lb(start[t]));
    //EX_PUSH(expl, start[t] > ub(start[t]));
    eff_lst = std::max(eff_lst, t_ub);
  }
  //EX_PUSH(expl, start[ex_task] < lb(start[ex_task]));
  EX_PUSH(expl, start[ex_task] <= eff_lst - du[ex_task]);
  ex_sz = 0;
}

void disjunctive::ex_ub_dp(int ex_task, pval_t p, vec<clause_elt>& expl) {
  // Set up the data structures
  for(int ii : irange(sz)) {
    est[ii] = -ub(start[ii]) - du[ii];
    lct[ii] = -lb(start[ii]);
  }
  ex_dp(ex_task, -start[ex_task].ub_of_pval(p) - du[ex_task]);
   // FIXME: Probably not quite right.
  int ex_lst = -est[ex_task] - du[ex_task];
  int eff_ect = INT_MAX;
  for(int t : range(ex_buf, ex_buf + ex_sz)) {
    int t_lb = std::max(-env_u, ex_lst+1-du[t]);
    EX_PUSH(expl, start[t] < t_lb);
    EX_PUSH(expl, start[t] > -env_l - du[t]);
    //EX_PUSH(expl, start[t] < lb(start[t]));
    //EX_PUSH(expl, start[t] > ub(start[t]));
    eff_ect = std::min(eff_ect, t_lb+du[t]);
  }
  EX_PUSH(expl, start[ex_task] >= eff_ect);
  // EX_PUSH(expl, start[ex_task] > ub(start[ex_task]));
  ex_sz = 0;
}

// Naive O(n^2) overload checking.
bool disjunctive::check_sat(ctx_t& ctx) {
  // Identify the envelope starts.
  // First, try the relatively cheap checks
  // for edge-finding.
  vec<int> ss;
  vec<int> e_perm;
  for(int xi : irange(sz)) {
    ss.push(start[xi].lb(ctx));
    e_perm.push(xi);
  }
  uniq(ss);
  std::sort(e_perm.begin(), e_perm.end(),
            [this, &ctx](int i, int j) { return start[i].ub(ctx) + du[i] < start[j].ub(ctx) + du[j]; });

  // For each possible start, check if there is any over-full envelope
  // it defines.
  for(int s : ss) {
    int ect = s;
    for(int t : e_perm) {
      if(s <= start[t].lb(ctx)) {
        // Contained in the envelope
        ect += du[t]; 
        if(start[t].ub(ctx) + du[t] < ect)
          return false;
      }
    }
  }

  // We've covered all the edgefinding cases, but there's also detectable
  // precedence reasoning we might have missed.
  #if 0
  for(int s : ss) {
    int est = s;
    int sum = 0;

    auto it = e_perm.begin();
    auto en = e_perm.end();
    for(; it != en; ++it) {
      int t = *it;
      if(s > start[t].lb(ctx))
        continue;
      int lct = start[t].ub(ctx) + du[t];
      sum += du[t];

      auto prec = it;
      for(++prec; prec != en; ++prec) {
        int t_prec = *prec;
        int t_est = start[t_prec].lb(ctx);
        int t_lct = start[t_prec].ub(ctx) + du[t_prec];
        //if(t_est >= est)
        //  continue;
        int d_ov = std::min(du[t_prec],
                            std::min(t_est + du[t_prec] - est,
                                     lct - (t_lct - du[t_prec])));
        if(est + sum + d_ov > lct)
          return false;
      }
    }
  }
  return true;
  #endif
  // Fallthrough
  solver check;
  check.data->opts.global_diff = true;
  vec<geas::intvar> check_start;
  for(int t : irange(sz)) {
    int lb = start[t].lb(ctx);
    int ub = start[t].ub(ctx);
    check_start.push(check.new_intvar(lb, ub));
  }
  // Now add the mutual exclusion constraints
  for(int t : irange(sz)) {
    for(int u : irange(t+1, sz)) {
      geas::patom_t r = check.new_boolvar();
      int_le(check.data, check_start[t], check_start[u], -du[t], r);
      int_le(check.data, check_start[u], check_start[t], -du[u], ~r);
    }
  }
  if(check.solve() != solver::result::SAT)
    return false;

  auto m = check.get_model();
  vec<int> t_perm;
  for(int i : irange(sz))
    t_perm.push(i);
  std::sort(t_perm.begin(), t_perm.end(),
            [&m,&check_start](int i, int j) { return m[check_start[i]] < m[check_start[j]]; });
  fprintf(stderr, "%% model: [");
  for(int t : t_perm)
    fprintf(stderr, " %d:%d->%d", t, m[check_start[t]], m[check_start[t]]+du[t]);
  fprintf(stderr, "]\n");
  return true;
}

enum SchedKey { T_EST = 0, T_ECT = 1, T_LST = 2, T_LCT = 3, T_COUNT = 4 };
struct sched_info {
  int idx[T_COUNT];
};
void disjunctive::dump_schedule(void) {
  // FIXME: Also gotta render ect, lst.
  auto key = [this](unsigned tag) {
    unsigned t = (tag >> 2);
    switch(tag & 3) {
    case T_EST: 
      return est[t];
    case T_ECT:
      return est[t] + du[t];
    case T_LST:
      return lct[t] - du[t];
    case T_LCT:
      return lct[t];
    }
    // Unreachable
    return 0;
  };

  vec<int> landmarks;
  vec<unsigned> tag_perm;
  vec<sched_info> info;
  for(int t : irange(sz)) {
    info.push();
    tag_perm.push( (t << 2) | T_EST);
    tag_perm.push( (t << 2) | T_ECT);
    tag_perm.push( (t << 2) | T_LST);
    tag_perm.push( (t << 2) | T_LCT);
  }
  std::sort(tag_perm.begin(), tag_perm.end(), 
            [key](unsigned s, unsigned t) { return key(s) < key(t); });

  auto it = tag_perm.begin();
  auto en = tag_perm.end();

  int l = key(*it);
  int idx = landmarks.size();
  landmarks.push(l);
  for(; it != en; ++it) {
    if(key(*it) != l) {
      idx = landmarks.size();
      l = key(*it);
      landmarks.push(l);
    }

    int t = (*it) >> 2;
    info[t].idx[ (*it) & 3 ] = idx;
  }

  // Now we render.
  fprintf(stderr, "% Landmarks: [%d", landmarks[0]);
  for(int l : landmarks.tail())
    fprintf(stderr, ", %d", l);
  fprintf(stderr, "]\n");

  int M = landmarks.size();
  for(int t : irange(sz)) {
    const auto i(info[t]);
    int st = i.idx[T_EST];
    int en = i.idx[T_LCT];
    fprintf(stderr, "|");
    int ii = 0;
    for(; ii < st; ++ii)
      fprintf(stderr, ".");
    fprintf(stderr, "["); ++ii;

    int ec = i.idx[T_ECT];
    int ls = i.idx[T_LST];

    if(ec <= ls) {
      for(; ii < ec; ++ii)
        fprintf(stderr, "=");
      for(; ii < ls; ++ii)
        fprintf(stderr, "-");
    } else {
      for(; ii < ls; ++ii)
        fprintf(stderr, "=");
      for(; ii < ec; ++ii)
        fprintf(stderr, "x");
    }
    for(; ii < en; ++ii)
      fprintf(stderr, "=");
    fprintf(stderr, "]"); ++ii;
    for(; ii < M; ++ii)
      fprintf(stderr, ".");
    fprintf(stderr, "| t%d\n", t);
  }
}

bool disjunctive_int(solver_data* s, vec<intvar>& st, vec<int>& du) {
  // new disjunctive(s, st, du);
  // return true;
  return disjunctive::post(s, st, du);
}

bool disjunctive_var(solver_data* s, vec<intvar>& st, vec<intvar>& du) {
  // new disj_var(s, st, du);
  GEAS_NOT_YET;
  return false;
}

}
