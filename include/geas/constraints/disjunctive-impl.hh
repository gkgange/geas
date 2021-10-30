#ifndef GEAS__DISJUNCTIVE_IMPL__HH
#define GEAS__DISJUNCTIVE_IMPL__HH

// Utility stuff for dealing with disjunctive scheduling constraints.

namespace geas {

// ImpHeap interprets a buffer as a heap, using a given comparator.
// Just saves us from having to have a bunch of heaps sitting around.
struct ImpHeap {
  static int left(int p) { return (p << 1)+1; }

  template<class Cmp>
  static void percolate_down(Cmp cmp, int* mem, int sz, int p) {
    int item = mem[p];
    int c = left(p);
    while(c < sz) {
      c += (c+1 < sz) && cmp(mem[c+1], mem[c]);
      if(!cmp(mem[c], item))
        break;
      mem[p] = mem[c];
      p = c;
      c = left(p);
    }
    mem[p] = item;
  }

  template<class Cmp>
  static void heapify(Cmp cmp, int* begin, int* end) {
    int sz = end - begin;
    for(int p = sz/2; p >= 0; --p)
      percolate_down(cmp, begin, sz, p);
  }
  
  // Returns the top of the heap, but also swaps it to
  // the end (so we can read out the sorted items from
  // right to left).
  template<class Cmp>
  static int pop(Cmp cmp, int* begin, int*& end) {
    assert(begin < end);
    int top = *begin;
    --end;
    std::swap(*begin, *end);
    if(end - begin > 1)
      percolate_down(cmp, begin, end - begin, 0);
    return top;
  }
};

template<class Var, class Val>
struct disj_val {
  struct task {
    Var start;
    Val dur;

    Val est(const ctx_t& ctx) const { return start.lb(ctx); }
    Val lst(const ctx_t& ctx) const { return start.ub(ctx); }

    Val ect(const ctx_t& ctx) const { return start.lb(ctx) + dur; }
    Val lct(const ctx_t& ctx) const { return start.ub(ctx) + dur; }
  };

  template<class ItT, class ItV>
  void fill_est(const ctx_t& ctx, ItT it, ItT en, ItV dest) {
    for(; it != en; ++it, ++dest) {
      *dest = (*it).est(ctx);
    }
  }

  template<class ItT, class ItV>
  void fill_inv_lct(const ctx_t& ctx, ItT it, ItT en, ItV dest) {
    for(; it != en; ++it, ++dest) {
      *dest = -(*it).lct(ctx);
    }
  }
};

};

#endif
