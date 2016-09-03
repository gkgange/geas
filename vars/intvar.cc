#include "solver/solver_data.h"
#include "vars/intvar.h"

#include <cstdio>
#include <utility>

namespace phage {

intvar_base::intvar_base(solver_data* _s, intvar_manager* _m, int _idx, pid_t _pid)
  : s(_s), man(_m), idx(_idx), pid(_pid)
{ assert(!(pid&1)); }

int64_t intvar_base::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

int64_t intvar_base::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}

int64_t intvar_base::lb_prev(void) const {
  return to_int(s->state.p_last[pid]);
}

int64_t intvar_base::ub_prev(void) const {
  return to_int(pval_max - s->state.p_last[pid^1]);
}

int64_t intvar_base::lb_0(void) const {
  return to_int(s->state.p_root[pid]);
}

int64_t intvar_base::ub_0(void) const {
  return to_int(pval_max - s->state.p_root[pid^1]);
}

bool intvar_base::set_lb(int64_t min, reason r) {
  return enqueue(*s, patom_t(pid, from_int(min)), r);
}

bool intvar_base::set_ub(int64_t max, reason r) {
  return enqueue(*s, patom_t(pid^1, pval_max - from_int(max)), r);
}

int64_t intvar_base::model_val(const model& m) const {
  return to_int(m.get(pid));
}

void intvar_base::attach(intvar_event e, watch_callback c) {
  man->attach(idx, e, c);
}

static void wakeup(void* ptr, int idx) {
  intvar_manager* man = static_cast<intvar_manager*>(ptr);
  // Do some stuff
  if(idx&1) {
    for(auto c : man->lb_callbacks[idx>>1])
      c();
  } else {
    for(auto c : man->ub_callbacks[idx>>1])
      c();
  }
  printf("Ping: %d\n", idx);
}

intvar_manager::intvar_manager(solver_data* _s)
  : s(_s) { }
     
intvar intvar_manager::new_var(int64_t lb, int64_t ub) {
  int idx = var_preds.size();
  pid_t p = new_pred(*s);
  var_preds.push(p);
  eqtable.push_back(std::unordered_map<pval_t, patom_t>());
  // Register this as a watcher.
  // GKG: Perhaps defer this until something
  // is attached to the var
  s->pred_callbacks[p].push(watch_callback(wakeup, this, idx<<1));
  s->pred_callbacks[p+1].push(watch_callback(wakeup, this, (idx<<1)|1));

  lb_callbacks.push();
  ub_callbacks.push();

  // fprintf(stdout, "[%lld,%lld] ~~> [%lld, %lld]\n", lb, ub, intvar::from_int(lb), intvar::from_int(ub));
  // Set bounds
  intvar v(new intvar_base(s, this, idx, p));
  v.set_lb(lb, nullptr);
  v.set_ub(ub, nullptr);
  // Also set the p_last and p_root values
  s->state.p_last[p] = from_int(lb);
  s->state.p_root[p] = from_int(lb);

  s->state.p_last[p^1] = pval_max - from_int(ub);
  s->state.p_root[p^1] = pval_max - from_int(ub);
  return v;
}

void intvar_manager::attach(unsigned int v_idx, intvar_event e, watch_callback c) {
  if(e&E_LB) {
    lb_callbacks[v_idx].push(c);  
  }
  if(e&E_UB) {
    ub_callbacks[v_idx].push(c);
  }
}

bool intvar_manager::in_domain(unsigned int vid, int64_t val) {
  NOT_YET;
  return false;
}

patom_t intvar_manager::make_eqatom(unsigned int vid, int64_t ival) {
  // Find the appropriate var/val pair
  pid_t x_pi(var_preds[vid]);
  pval_t val(from_int(ival));

  auto it = eqtable[vid].find(val);
  if(it != eqtable[vid].end())
    return (*it).second;

  // Allocate the atom
  // FIXME: Deal with duplicates
  patom_t at(new_bool(*s));

  // Connect it to the corresponding bounds
  add_clause(s, ~at, patom_t(x_pi, val));
  add_clause(s, ~at, ~patom_t(x_pi, val+1));
  add_clause(s, at, ~patom_t(x_pi, val), patom_t(x_pi, val+1));

  eqtable[vid].insert(std::make_pair(val, at));

  return at;
}

}

