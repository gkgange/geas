#if 0
#include <climits>
#include <unordered_map>

#include <geas/utils/bitops.h>
#include <geas/solver/solver_debug.h>
#include <geas/solver/solver_data.h>
#include <geas/solver/solver_ext.h>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>
#include <geas/mtl/bool-set.h>

#include <geas/utils/mergeable-map.h>
#include <geas/constraints/partial-order.hh>
using namespace geas;

void partial_order::red_add(int s, int d) {
  red_bits[s][B64::block(d)] |= B64::bit(d);
  red_succ[s].add(d);
  red_pred[d].add(s);
}
void partial_order::red_remove(int s, int d) {
  red_bits[s][B64::block(d)] &= ~B64::bit(d);
  red_succ[s].remove(d);
  red_pred[d].remove(s);
}

bool partial_order::is_prec(int s, int d) const {
  return trans_succ[s][B64::block(d)] & B64::bit(d);
}

void partial_order::build_topo_rec(int curr) {
  if(_flags[B64::block(curr)] & B64::bit(curr))
    return;

  _flags[B64::block(curr)] |= B64::bit(curr);
  for(int pred : _red_pred[curr])
    build_topo_rec(curr);
  _topo[_topo_hd++] = curr;
}

void partial_order::build_topo(void) {
  // We'll be using the _flags to mark which nodes have
  // already been encountered.
  topo_hd = 0;
  int sz = size();
  for(int ii = 0; ii < sz; ++ii)
    build_topo_rec(ii);
  memset(_flags.begin(), 0, sizeof(uint64_t) * _flags.size());
}

bool partial_order::add_prec(int s, int d) {
  // First, check that it isn't already inconsistent.
  if(trans_succ[d].elem(s))
    return false;
  // Or already implied.
  if(trans_succ[s].elem(d))
    return true;

  // If it's not already implied, (s, d) should be
  // in the transitive reduction.
  red_add(s, d);
  for(int w : trans_succ[d].words()) {
    close_dfs(s, w, trans_succ[d][w]);
  }
  return true;
}

// Add any successors which aren't already present.
bool partial_order::close_dfs(int s, int word, uint64_t mask) {
  // Identified new successors
  uint64_t src_mask(mask & ~trans_succ[s][word]);
  if(src_mask) {
    trail_change(s->persist,
                 trans_succ[s][word],
                 trans_succ[s][word] | mask);
    // trans_succ[s][word] |= mask;
    for(int pred : red_pred[s])
      close_dfs(pred, word, src_mask);

    if(src_mask & reif_inv[s][word]) {
      // Some reification variables need to be set false (if not already)
      uint64_t to_deact(mask & reif_inv[s][word]);
      for(int d : block_range(word, to_deact)) {
        // Do something
      }
    }
  }
  // Update the transitive reduction.
  // We need to check for any reduced edges from s to
  // nodes in (w, mask).
  if(mask & red_bits[s][word]) {
    uint64_t to_remove(mask & red_bits[s][word]);
    for(int d : block_range(word, to_remove)) {
      red_trail.push(RedEvent::rem(s, d));
      red_remove(s, d);
    }
  }
}

Timestamp partial_order::timestamp(void) const {
  return Timestamp { red_trail.size() };
}
void partial_order::set_cursor(Timestamp t) {
  if(t.pos < cursor) {
    // Undo modifications.
    for(const entry& e : rev_range(red_trail.begin() + t.pos,
                               red_trail.begin() + cursor)) {
      if(e.sign) { // Undoing a removal
        red_add(e.s, e.d);
      } else {
        red_remove(e.s, e.d);
      }
    }
  } else {
    for(const entr& e : range(red_trail.begin() + cursor,
                              red_trail.begin() + t.pos)) {
      // Apply changes
      if(e.sign) { // Applying removal
        red_remove(e.s, e.d);
      } else {
        red_add(e.s, e.d);
      }
    }
  }
  cursor = t.pos;
}

bool explain_rec(partial_order& p, int s, int d, vec<clause_elt>& expl) {
  // Early termination
  if(seen[d] || !is_prec(s, d))
    return false;
  seen[d] = true;

  for(int d_pred : p._red_pred[d]) {
    if(explain_rec(p, s, d_pred, expl)) {
      add_reason(p, s, d_pred, expl);
      return true;
    }
  }
  return false;
}
void clear_seen_preds(partial_order& p, int d) {
  if(!seen[d])
    return;

  seen[d] = false;
  for(int d_pred : p.red_preds[d])
    clear_seen_preds(p, d);
}

// We could also have set_cursor() update the transitive closure, in
// which case reading out the explanation would be much easier. 
void partial_order::explain(Timestamp t, int s, int d, vec<clause_elt>& expl) {
  // Update the internal state to the appropriate moment.
  set_cursor(t);

  // Easiest way to reconstruct the implication? We'll just run a DFS on predecessors
  // of d, cutting off early if we see a node we've already marked, or that isn't in
  // succ[s] (which is currently an overapproximation).
  if(!explain_rec(*this, s, d, expl))
    assert(0);
  // Clear seen markers
  clear_seen_preds(*this, d);
}

void partial_order::ex_impl(int reif_id, pval_t _p, vec<clause_elt>& confl) {
  const reif_info_t& r(reif_info[reif_id]);
  explain(r.time, r.d, r.s);
}

#endif
