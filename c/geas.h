#ifndef GEAS_H
#define GEAS_H
// Top-level C interface
#include "c/atom.h"
#include "solver/stats.h"
#include "solver/options.h"

#ifdef __cplusplus
#include <cstdio>
extern "C" {
#else
#include <stdio.h>
#endif

typedef enum { SAT, UNSAT, UNKNOWN } result;

struct solver_s;
typedef struct solver_s* solver;

struct intvar_s;
typedef struct intvar_s* intvar;
struct fpvar_s;
typedef struct fpvar_s* fpvar;

/*
struct opt_intvar_s;
typedef struct opt_intvar_s* opt_intvar;
*/

struct model_s;
typedef struct model_s* model;

struct brancher_s;
typedef struct brancher_s* brancher;

/*
typedef struct {
  int solutions;
  int conflicts;
  int restarts;
} stats;

// Urgh. Should just have stats and options as straight structs.
typedef struct {
  int learnt_dbmax;
  double learnt_growthrate;
  
  double pred_act_inc;
  double pred_act_decay;

  double learnt_act_inc;
  double learnt_act_decay;

  int restart_limit;
  double restart_growthrate;
} options;
*/

options default_opts(void);
solver new_solver(options opts);
void destroy_solver(solver);

intvar new_intvar(solver, int lb, int ub);
void destroy_intvar(intvar);
intvar permute_intvar(solver, intvar, int* vals, int sz);
int make_sparse(intvar, int* vals, int sz);
intvar intvar_neg(intvar);
intvar intvar_plus(intvar, int);

/*
opt_intvar new_opt_intvar(solver, int lb, int ub);
opt_intvar intvar_make_opt(solver, intvar v);
void destroy_opt_intvar(intvar);
*/

fpvar new_floatvar(solver, float lb, float ub);
void destroy_floatvar(fpvar);

atom new_boolvar(solver);

void set_int_polarity(intvar, int);
void set_bool_polarity(solver, atom, int);

typedef enum { VAR_INORDER, VAR_FIRSTFAIL, VAR_LEAST, VAR_GREATEST } var_choice;
typedef enum { VAL_MIN, VAL_MAX, VAL_SPLIT } val_choice;

brancher new_int_brancher(var_choice, val_choice, intvar*, int);
brancher new_bool_brancher(var_choice, val_choice, atom*, int);
brancher new_int_priority_brancher(var_choice, intvar*, int, brancher*, int);
brancher new_bool_priority_brancher(var_choice, atom*, int, brancher*, int);
brancher seq_brancher(brancher*, int);
brancher limit_brancher(brancher);
void add_brancher(solver, brancher);

result solve(solver, int);
void abort_solve(solver);

int post_atom(solver, atom);
int post_clause(solver, atom*, int);

int assume(solver, atom);
void retract(solver);
void retract_all(solver);
void get_conflict(solver, atom**, int*);

model get_model(solver);
void destroy_model(model);

int int_value(model, intvar);
float float_value(model, fpvar);
int atom_value(model, atom);

pid_t ivar_pid(intvar);
int ivar_lb(intvar);
int ivar_ub(intvar);

atom ivar_le(intvar, int);
atom ivar_eq(intvar, int);
atom fpvar_le(fpvar, float);
atom fpvar_lt(fpvar, float);

pred_t new_pred(solver, int, int);
atom pred_ge(pred_t, int);

statistics get_statistics(solver);

// Proof logging
void set_log_file(solver, FILE*);
void set_cons_id(solver, int);
#ifdef __cplusplus
}
#endif

#endif
