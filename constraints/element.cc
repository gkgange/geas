#include <utility>
#include <algorithm>
#include "engine/propagator.h"
#include "solver/solver_data.h"
#include "vars/intvar.h"

namespace phage {

typedef std::pair<int, int> ipair;

void int_element(solver_data* s, patom_t r, intvar x, intvar z,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  if(s->state.is_entailed_l0(r)) {
    x.set_lb(base, reason()); x.set_ub(base + ys.size()-1, reason());  
    // z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

    make_sparse(z, ys);
  } else {
    add_clause(s, ~r, x >= base);
    add_clause(s, ~r, x < base + ys.size());

    vec<clause_elt> ps { ~r };
    for(int y : ys)
      ps.push(z == y);
    add_clause(*s, ps);
  }

  for(int ii : irange(ys.size())) {
    add_clause(s, ~r, x != ii + base, z == ys[ii]);
  }

  vec<int> ys_uniq(ys); uniq(ys_uniq);

  for(int yy : ys_uniq) {
    vec<clause_elt> ps { ~r };
    ps.push(z != yy);
    for(int ii : irange(ys.size())) {
      if(ys[ii] == yy) {
        ps.push(x == ii + base);
      }
    }
    add_clause(*s, ps);
  }

  return;
}

class elem_var_bnd : public propagator, public prop_inst<elem_var_bnd> {
  // Wakeup and explanation
  static void wake_x(void* ptr, int xi) {
    elem_var_bnd* p(static_cast<elem_var_bnd*>(ptr)); 
    p->queue_prop();     
  }
  static void wake_z(void* ptr, int yi) {
    elem_var_bnd* p(static_cast<elem_var_bnd*>(ptr)); 
    p->queue_prop();     
  }
  static void wake_r(void* ptr, int dummy) {
    elem_var_bnd* p(static_cast<elem_var_bnd*>(ptr)); 
    p->queue_prop();
  }

public:
  elem_var_bnd(solver_data* s, intvar _x, intvar _z, vec<intvar>& _ys, patom_t _r)
    : propagator(s), x(_x), z(_z), ys(_ys), r(_r) {
     
  }

  void root_simplify(void) {
    
  }
    
   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_bnd]]" << std::endl;
#endif

      return true;
    }

    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;
};

void int_element(solver_data* s, intvar x, intvar z, vec<int>& ys, patom_t r) {
  int_element(s, r, x, z, ys, 1);
}

void intvar_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys, patom_t r) {
  NOT_YET;
  return; 
}
}
