#ifndef GEAS__DIFFLOGIC__H
#define GEAS__DIFFLOGIC__H
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>
#include <geas/solver/branch.h>

namespace geas {

namespace difflogic {
  // r -> (x - y <= k)
  bool post_base(solver_data* s, patom_t r, intvar x, intvar y, int k);
  bool post_bv(solver_data* s, patom_t r, intvar x, intvar y, int k);
  inline bool post(solver_data* s, patom_t r, intvar x, intvar y, int k) {
    return post_bv(s, r, x, y, k);
  }
  bool check_sat(solver_data* s, intvar x, intvar y, int k);
  bool check_sat(solver_data* s, ctx_t& ctx, intvar x, intvar y, int k);

  brancher* branch_order(solver_data* s, VarChoice varc, ValChoice valc, vec<intvar>& xs);
}

}

#endif
