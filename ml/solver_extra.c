#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>

#include <geas/solver/stats.h>
#include <geas/solver/options.h>
#include <geas/c/geas.h>

extern value camlidl_c2ml_atom_atom(atom *, camlidl_ctx _ctx);
extern void camlidl_ml2c_atom_atom(value, atom *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_brancher(brancher *, camlidl_ctx _ctx);

CAMLprim value ml_get_conflict(value _s) {
  CAMLparam1 (_s);
  CAMLlocal2 (_at, _res);
  
  atom* arr;
  int sz;
  int ii; 
  
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  get_conflict(*((solver*) Data_custom_val(_s)), &arr, &sz);
  
  _res = caml_alloc(sz, 0);
  for(ii = 0; ii < sz; ii++) {
    _at = camlidl_c2ml_atom_atom(arr+ii, _ctx);
    Store_field(_res, ii, _at);
  }
  camlidl_free(_ctx);
  free(arr);
  CAMLreturn (_res);
}

CAMLprim value ml_assumption_inferences(value _s) {
  CAMLparam1 (_s);
  CAMLlocal2 (_at, _res);
  
  atom* arr;
  int sz;
  int ii; 
  
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  get_assumption_inferences(*((solver*) Data_custom_val(_s)), &arr, &sz);
  
  _res = caml_alloc(sz, 0);
  for(ii = 0; ii < sz; ii++) {
    _at = camlidl_c2ml_atom_atom(arr+ii, _ctx);
    Store_field(_res, ii, _at);
  }
  camlidl_free(_ctx);
  free(arr);
  CAMLreturn (_res);
}

atom call_ml_brancher(void* closure) {
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  atom res_atom;
  camlidl_ml2c_atom_atom(caml_callback(*((value*) closure), Val_unit), &res_atom, _ctx);
  camlidl_free(_ctx);

  return res_atom;
}

void finalize_ml_brancher(void* closure) {
  CAMLparam0();
  caml_remove_global_root((value*) closure);
  CAMLreturn0;
}

value ml_external_brancher(value _callback) {
  CAMLparam1 (_callback);
  CAMLlocal1 (_brancher);

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  value* mem = malloc(sizeof(value));
  *mem = _callback;
  caml_register_global_root(mem);
  brancher b = external_brancher(call_ml_brancher, finalize_ml_brancher, (void*) mem);

  _brancher = camlidl_c2ml_solver_brancher(&b, _ctx);
  camlidl_free(_ctx);
  CAMLreturn (_brancher);
}

CAMLprim value ml_get_ivar_activities(value _s, value _xs) {
  CAMLparam2 (_s, _xs);
  CAMLlocal1 (_acts);
  
  // This is kind of double-handling. Would be more efficient to
  // bypass the C interface...
  int sz = Wosize_val(_xs);

  intvar* xs = (intvar*) malloc(sizeof(intvar) * sz);
  for(int ii = 0; ii < sz; ++ii) {
    xs[ii] = *((intvar*) Data_custom_val(Field(_xs, ii)));
  }
  double* c_acts = NULL; // Allocated by callee
  get_ivar_activities(*((solver*) Data_custom_val(_s)), xs, sz, &c_acts);

  _acts = caml_alloc(sz, Double_array_tag);
  for(int ii = 0; ii < sz; ii++) {
    Store_double_field(_acts, ii, c_acts[ii]);
  }
  free(xs);
  free(c_acts);

  CAMLreturn (_acts);
}
