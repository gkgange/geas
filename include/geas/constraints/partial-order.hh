#ifndef GEAS__PARTIAL_ORDER__HH
#define GEAS__PARTIAL_ORDER__HH
#include <geas/utils/mergeable-map.hh>
#include <geas/engine/geas-types.h>

#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>

// Structure for maintaining 
namespace geas {

// Not *exactly* a propagator, but shares most of the same
// behaviours.
/*
struct partial_order {
  partial_order(int sz);

  bool is_prec(int s, int d) const;
  
  // Need to be careful with this reason -- if we need
  // to backtrack to resolve r, bad things can happen.
  bool make_prec(int s, int d, reason r); 
  void explain_prec(vec<clause_elt>& confl, int s, int d);

  // Interface for iteration?
  // Iterating over all predecessors/successors
  // And over just immediate (reduced) predecessors/successors.
  struct vert_range;
  vert_range immediate_preds(void);
  vert_range immediate_succs(void);
  
  struct cell_range;
  cell_range preds(void);
  cell_range succs(void);
};
*/

// Tracks *strict* precedences for a partially-ordered set.
// We're relying on the successor relation being acyclic.
struct partial_order {
  // Should really come up with a proper interface for this kind of stuff.
  // Even if it's view-based like the ImpHeap.
  struct Timestamp {
    int pos;
  };
  struct RedEvent {
    static RedEvent add(unsigned s, unsigned d) { return RedEvent { s, d, 0 }; }
    static RedEvent rem(unsigned s, unsigned d) { return RedEvent { s, d, 1 }; }

    unsigned s : 32;
    unsigned d : 31;
    unsigned sign : 1;
  };
  
  struct adj_iterator {
    uint64_t mask;
    int* word_ptr;

    uint64_t* base;

    int operator*(void) const { assert(mask); return __builtin_ctzll(mask) + (*word_ptr) << B64::block_bits(); }
    // FIXME: Be careful of sentinel word_ptr.
    adj_iterator& operator++(void) {
      mask &= mask-1;
      if(!mask) {
        ++word_ptr;
        mask = base[*word_ptr];
      }
    }
    // FIXME: Only works if o is the end iterator, so don't
    // use it with others in the middle.
    bool operator!=(const adj_iterator& o) const {
      return word_ptr != o.word_ptr;
    }
  };

  struct adj {
    uint64_t* bits;
    int* words;
    int words_sz;

    adj_iterator begin(void) const;
    adj_iterator end(void) const;
  };

  int size(void) const { return trans_succ.size(); }

  // Inspection
  bool is_prec(int s, int d) const;

  // Mutation
  bool add_prec(int s, int d, reason r);
  void close_dfs(int s, int word, uint64_t mask);

  void red_add(int s, int d);
  void red_remove(int s, int d);

  // Iteration
  void build_topo(void); // Construct consistent linear extension.
  void _build_topo_rec(int n);

  // For generating explanations
  Timestamp timestamp(void) const;
  void set_cursor(Timestamp); // Reset the trans. red to the given moment.
  void explain(Timestamp t, int s, int d, vec<clause_elt>& expl);
  void ex_impl(int tag, pval_t _p, vec<clause_elt>& confl);

  // Reifying inequalities. For now, we're assuming
  // all relations are strict (so, disjunctive)
  patom_t get_strict(int s, int d);
  
  // Base representation.
  //====================
  // We store the forward transitive closure of the graph,
  // and the backwards transitive reduction.
  vec<adj> trans_succ;

  vec<uint64_t*> red_bits;
  vec<trieset> red_pred;
  vec<trieset> red_succ;

  // Restriction on the reasons: they must be available
  // retroactively (so atom/clauses is fine, but thunks
  // must *not* have Ex_BTPRED set).
  vec<reason> reasons;
  Tint reason_sz;

  // Reification variable bookkeeping
  reif_map_t reif_map;
  vec<reif_info_t> reif_info;
  // Is there a reif var for (d, s) which needs to be flipped off
  // if (s, d) is entailed?
  vec<uint64_t*> reif_inv;

  // Scratch space buffers.
  vec<uint64_t> _flags;
  vec<int> _topo;
  int _topo_hd;

  // Trailing changes
  vec<RedEvent> red_trail;
  int cursor; // Current position in the trail
};


}

#endif
