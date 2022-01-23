#include <iostream>
#include <cstdio>
#include <geas/solver/solver.h>
#include <geas/solver/solver_data.h>

#include <geas/constraints/builtins.h>

vec<geas::patom_t> boolvec(geas::solver_data* s, int N) {
  vec<geas::patom_t> xs;
  for(int ii = 0; ii < N; ++ii)
    xs.push(new_bool(*s));
  return xs;
}
int test_atmost1() {
  int N = 11;

  {
    geas::solver s;
    geas::solver_data* sd(s.data);

    vec<geas::patom_t> xs(boolvec(sd, N));
    atmost_1(sd, xs);

    for(int ii = 0; ii < N; ++ii) {
      s.assume(xs[ii]);
      assert(s.solve() == geas::solver::SAT);
      for(int jj = ii+1; jj < N; ++jj) {
        s.assume(xs[jj]);
        assert(s.solve() == geas::solver::UNSAT);
        s.retract();
      }
      s.retract();
    }
  }

  {
    geas::solver s;
    geas::solver_data* sd(s.data);

    geas::patom_t r(s.new_boolvar());
    vec<geas::patom_t> xs(boolvec(sd, N));
    atmost_1(sd, xs, r);

    for(int ii = 0; ii < N; ++ii) {
      s.assume(xs[ii]);
      s.assume(r);
      assert(s.solve() == geas::solver::SAT);
      s.retract();

      for(int jj = ii+1; jj < N; ++jj) {
        s.assume(xs[jj]);
        assert(s.solve() == geas::solver::SAT);

        s.assume(r);
        assert(s.solve() == geas::solver::UNSAT);
        s.retract();
        s.retract();
      }
      s.retract();
    }
  }
}

int test_linear_le() {
  {
    geas::solver s;
    geas::solver_data* sd(s.data);
    geas::patom_t r(s.new_boolvar());
    vec<int> cs { 1, -1, 2, 2, 5, 6 };
    vec<geas::patom_t> xs(boolvec(sd, 6));
    bool_linear_le(sd, cs, xs, 4, r);

    for(auto at : xs)
      s.assume(at);
    assert(s.solve() == geas::solver::SAT);
    assert(!r.ub(sd->ctx()));
    s.clear_assumptions();

    s.assume(xs[5]);
    assert(s.solve() == geas::solver::SAT);
    s.assume(r);
    assert(s.solve() == geas::solver::UNSAT);
    s.retract();
    s.retract();

    s.assume(r);
    s.assume(xs[4]);
    assert(s.solve() == geas::solver::SAT);
    assert(!xs[0].ub(sd->ctx()));
    assert(xs[1].lb(sd->ctx()));

    s.retract();
    s.assume(xs[2]);
    s.assume(xs[3]);

    s.assume(xs[0]);
    assert(s.solve() == geas::solver::SAT);
    assert(xs[1].lb(sd->ctx()));

    s.retract();
    s.assume(~xs[1]);
    assert(s.solve() == geas::solver::SAT);
    assert(!xs[0].ub(sd->ctx()));
  }
}

int test_linear_ge() {
  {
    geas::solver s;
    geas::solver_data* sd(s.data);
    geas::patom_t r(s.new_boolvar());
    vec<int> cs { 1, 1, 2, 2, 3 };
    vec<geas::patom_t> xs(boolvec(sd, 5));
    bool_linear_ge(sd, cs, xs, 3, r);

    for(auto at : xs)
      s.assume(~at);
    assert(s.solve() == geas::solver::SAT);
    assert(!r.ub(sd->ctx()));
    s.clear_assumptions();

    s.assume(r);
    s.assume(~xs[4]);
    s.assume(~xs[3]);
    assert(s.solve() == geas::solver::SAT);
    assert(xs[2].lb(sd->ctx()));
    s.assume(~xs[0]);
    assert(s.solve() == geas::solver::SAT);
    assert(xs[1].lb(sd->ctx()));

    s.retract();
    s.assume(~xs[1]);
    assert(s.solve() == geas::solver::SAT);
    assert(xs[0].lb(sd->ctx()));
  }
}

int test_linear_conflict() {
  geas::solver s;
  geas::solver_data* sd(s.data);

  vec<int> cs { 1, 1, 2, 2, 3 };
  vec<geas::patom_t> xs(boolvec(sd, 5));

  bool_linear_le(sd, cs, xs, 4);
  bool_linear_ge(sd, cs, xs, 5);
  assert(s.solve() == geas::solver::UNSAT);
}

int main(int argc, char** argv) {
  test_atmost1();
  test_linear_le();
  test_linear_ge();
  test_linear_conflict();
}
