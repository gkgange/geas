#include <iostream>
#include <cstdio>
#include <geas/solver/solver.h>
#include <geas/solver/solver_data.h>

#include <geas/constraints/builtins.h>

using namespace geas;

std::ostream& operator<<(std::ostream& o, const solver::result& r) {
  switch(r) {
    case solver::SAT:
      o << "SAT";
      break;
    case solver::UNSAT:
      o << "UNSAT";
      break;
    default:
      o << "UNKNOWN";
  }
  return o;
}
void test1(void) {
  solver s;
  solver_data* sd(s.data);

  std::cout << "Testing iabs. Expected: SAT" << std::endl;

  intvar z = s.new_intvar(-10, 10);
  intvar x = s.new_intvar(-10, 10);

  int_abs(sd, z, x); 
  add_clause(sd, x < 0, z < 0);
  add_clause(sd, x >= -5, z <= 5);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[z, x] ~> [%lld, %lld]\n", m[z], m[x]);
  }
}

void test2(void) {
  solver s;
  solver_data* sd(s.data);

  std::cout << "Testing imul. Expected: SAT" << std::endl;

  intvar z = s.new_intvar(1, 10);
  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 0);

//  add_clause(sd, x < -2, x > 2);
//  add_clause(sd, y < -2, y > 2);

  int_mul(sd, z, x, y);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[z, x, y] ~> [%lld, %lld, %lld]\n", m[z], m[x], m[y]);
  }
}

void test3(void) {
  solver s;
  solver_data* sd(s.data);

  std::cout << "Testing imul. Expected: SAT" << std::endl;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);

  patom_t b = s.new_boolvar();

  int_le(sd, y, x, 0, b);
  int_le(sd, x, y, 0, ~b);
  add_clause(sd, ~b, x < 5);
  add_clause(sd, b, x < -5);

  if(!enqueue(*sd, ~b, reason()))
    GEAS_ERROR;
  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[b, x, y] ~> [%d, %lld, %lld]\n", m.value(b), m[x], m[y]);
  }
}

void testMax(void) {
  {
    solver s;
    solver_data* sd(s.data);
  
    intvar z = s.new_intvar(-20, 20);
    intvar x = s.new_intvar(-20, 20);
    intvar y = s.new_intvar(-20, 20);
    vec<intvar> xs { x, y };
    int_max(sd, z, xs);

    assert(s.is_consistent());
    s.assume(x >= 5);
    s.assume(y <= 0);
    assert(s.is_consistent());
    assert(z.lb(sd->ctx()) == 5);
    s.assume(z >= 2);
    solver::result r = s.solve();
    assert(r == solver::SAT);

    s.clear_assumptions();
    s.assume(y <= 0);
    s.assume(z >= 5);
    assert(s.is_consistent());
    assert(x.lb(sd->ctx()) == 5);
  }

  {
    solver s;
    intvar z = s.new_intvar(-20, 20);
    intvar x = s.new_intvar(10, 20);
    intvar y = s.new_intvar(-20, 14);
    vec<intvar> xs { x, y };
    int_max(s.data, z, xs);
    assert(s.is_consistent());
    assert(z.lb(s.data->ctx()) == 10);
    s.assume(z <= 11);
    assert(s.is_consistent());
    assert(x.ub(s.data->ctx()) == 11);
    assert(y.ub(s.data->ctx()) == 11);
    s.retract();
    s.assume(x >= 16);
    assert(s.is_consistent());
    assert(z.lb(s.data->ctx()) == 16);
  }
}
  
int main(int argc, char** argv) {
  test1();
  test2();
  test3();
  
  testMax();

  return 0;
}
