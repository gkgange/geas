#ifndef PHAGE_VAR__H
#define PHAGE_VAR__H
#include <unordered_map>

#include "utils/interval.h"
#include "engine/infer.h"
#include "solver/model.h"
#include "solver/solver_data.h"

namespace phage {

class intvar_manager;

enum intvar_event { E_None = 0, E_LB = 1, E_UB = 2, E_LU = 3, E_FIX = 4 };

// Extra bookkeeping for intvars
struct ivar_ext {
  ivar_ext(solver_data* _s, pid_t _p, int _idx)
    : s(_s), p(_p), idx(_idx) { }

  patom_t get_eqatom(pval_t val);
  void make_eager(void);
  bool make_sparse(vec<pval_t>& vs);

  solver_data* s;
  pid_t p;
  int idx;

  vec<watch_callback> b_callbacks[2];
  vec<watch_callback> fix_callbacks;

  std::unordered_map<pval_t, patom_t> eqtable;
  vec<pval_t> vals;
};

class intvar {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 
  // static const pval_t offset = ((pval_t) INT32_MIN); 

public:
#ifdef PVAL_32
  typedef int32_t val_t;
#else
  typedef int64_t val_t;
#endif

  static val_t to_int(pval_t v) { return (val_t) (offset + v); }
  static pval_t from_int(val_t v) { return ((pval_t) v) - offset; }

  // intvar_base(solver_data* _s, intvar_manager* _man, int idx, pid_t p);
  intvar(pid_t _p, int _off, ivar_ext* _ext)
    : p(_p), off(_off), ext(_ext) { }

  intvar(void)
    : p(0), off(0), ext(nullptr) { }

  intvar(const intvar& o)
    : p(o.p), off(o.off), ext(o.ext) { }

  intvar& operator=(const intvar& o) {
    p = o.p;
    off = o.off;
    ext = o.ext;
    return *this;
  }

  intvar operator-(void) const {
    return intvar(p^1, -off-2, ext);
  }
  intvar operator+(int k) const {
    return intvar(p, off+k, ext);
  }
  intvar operator-(int k) const {
    return intvar(p, off-k, ext);
  }

  val_t lb(const vec<pval_t>& ctx) const;
  val_t ub(const vec<pval_t>& ctx) const;
  val_t lb(const solver_data* s) const;
  val_t ub(const solver_data* s) const;

  /*
  val_t lb(void) const;
  val_t ub(void) const;
  */

  bool is_fixed(const vec<pval_t>& ctx) const;
  bool is_fixed(const solver_data*) const;
  /*
  bool is_fixed(void) const;

  val_t lb_prev(void) const;
  val_t ub_prev(void) const;

  val_t lb_0(void) const;
  val_t ub_0(void) const;
  */

  /*
  bool set_lb(val_t min, reason r);
  bool set_ub(val_t max, reason r);
  */

  void attach(intvar_event e, watch_callback c);

  // FIXME: Update to deal with sparse
  num_range_t<val_t> domain(ctx_t& ctx) const {
    return num_range(lb(ctx), ub(ctx)+1);
  }
  num_range_t<val_t> domain(solver_data* s) const;

  val_t model_val(const model& m) const;

  patom_t operator>=(val_t v) { return patom_t(p, from_int(v-off)); }
  patom_t operator>(val_t v) { return patom_t(p, from_int(v-off+1)); }
  patom_t operator<=(val_t v) { return ~patom_t(p, from_int(v-off+1)); }
  patom_t operator<(val_t v) { return ~patom_t(p, from_int(v-off)); }
  patom_t operator==(val_t v) {
    if(p&1) {
      // CHECK: Do we need to correct for negation here?
      return ~ext->get_eqatom(pval_inv(from_int(v)-off));
    } else {
      return ext->get_eqatom(from_int(v)-off);
    }
  }
  patom_t operator!=(val_t v) {
    if(p&1) {
      return ext->get_eqatom(pval_inv(from_int(v)-off));
    } else {
      return ~ext->get_eqatom(from_int(v)-off);
    }
  }

  /*
  solver_data* s;
  intvar_manager* man;
  int idx;
  pid_t pid;
  */
  pid_t p;
  val_t off;
  ivar_ext* ext;
};

class intvar_manager {
public:
  typedef intvar::val_t val_t;

  enum ivar_kind { IV_EAGER, IV_SPARSE, IV_LAZY };

  struct eq_elt { val_t val; patom_t atom; };
  struct eq_info { pid_t pid; pval_t val; };

  /*
  class var_data {
  public: 
    ivar_kind kind;
    pid_t pred;
     
    // In the eager case, it's just an array [with an offset]
    // In the sparse and lazy case, they're
    // hash tables.
    int base;
    eq_elt* elts;
    size_t elts_maxsz;
    size_t elts_count;
  };
  */

  intvar_manager(solver_data* _s);
     
  intvar new_var(val_t lb, val_t ub);

//  void attach(unsigned int vid, intvar_event e, watch_callback c);

  bool in_domain(unsigned int vid, val_t val);
  patom_t make_eqatom(unsigned int vid, val_t val);
  // bool make_sparse(unsigned int vid, vec<val_t>& vals);
  // void make_eager(unsigned int vid);

  vec<pid_t> var_preds;


  /*
  vec< vec<watch_callback> > lb_callbacks;
  vec< vec<watch_callback> > ub_callbacks;
  vec< vec<watch_callback> > fix_callbacks;

  // FIXME: Switch to a lighter-weight data-structure
  std::vector< std::unordered_map<pval_t, patom_t> > eqtable;
  vec<eq_info> eqinfo;
  */

  solver_data* s;
  vec<ivar_ext*> var_exts;
};

// inline patom_t intvar_base::operator==(int64_t v) {
/*
inline patom_t intvar::operator==(val_t v) {
  // return man->make_eqatom(idx, v);
  assert(0);
  return at_True;
}

// inline patom_t intvar_base::operator!=(int64_t v) {
inline patom_t intvar::operator!=(val_t v) {
  // return ~man->make_eqatom(idx, v);
  assert(0);
  return at_True;
}
*/

inline bool in_domain(intvar x, int k) {
//  return x.man->in_domain(x.idx, k);
  assert(0);
  return false;
}

template<class T>
// bool intvar_base::make_sparse(vec<T>& vals) {
bool make_sparse(intvar x, vec<T>& vals) {
  vec<pval_t> vs;
  if(x.p&1) {
    for(const T& v : vals)
      vs.push(pval_inv(intvar::from_int(v-x.off)));
  } else {
    for(const T& v : vals)
      vs.push(intvar::from_int(v-x.off));
  }
  return x.ext->make_sparse(vs);
}

inline void make_eager(intvar x) {
  x.ext->make_eager();
}

inline intvar::val_t to_int(pval_t v) { return intvar::to_int(v); }

inline pval_t from_int(intvar::val_t v) { return intvar::from_int(v); }


inline int_itv var_unsupp(solver_data* s, intvar x) {
  return int_itv { x.ub(s->state.p_root)+1, x.lb(s->state.p_root)-1 };
}

inline int_itv var_range(solver_data* s, intvar x) {
  return int_itv { x.lb(s), x.ub(s) };
}

// forceinline
inline intvar::val_t intvar::lb(const vec<pval_t>& ctx) const {
  return to_int(ctx[p]) + off;
}
// forceinline
inline intvar::val_t intvar::ub(const vec<pval_t>& ctx) const {
  return to_int(pval_inv(ctx[p^1])) + off;
}
inline intvar::val_t intvar::lb(const solver_data* s) const { return lb(s->state.p_vals); }
inline intvar::val_t intvar::ub(const solver_data* s) const { return ub(s->state.p_vals); }

inline bool intvar::is_fixed(const vec<pval_t>& ctx) const {
  return pred_fixed(ctx, p);
}
inline bool intvar::is_fixed(const solver_data* s) const { return is_fixed(s->state.p_vals); }

inline num_range_t<intvar::val_t> intvar::domain(solver_data* s) const { return domain(s->state.p_vals); }
/*
inline intvar::val_t intvar::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

// forceinline
inline intvar::val_t intvar::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}
*/

}
#endif
