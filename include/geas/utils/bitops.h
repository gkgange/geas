#ifndef GEAS__BITOPS__H
#define GEAS__BITOPS__H
// Helper header for doing stuff on BitMaps.
namespace geas {
  namespace B32 {
    inline unsigned block_bits(void) { return 5; }
    inline unsigned block_size(void) { return 1 << block_bits(); }
    inline uint64_t block_mask(void) { return block_size()-1; }
    inline unsigned num_blocks(unsigned sz) { return (sz >> block_bits()) + ((sz & block_mask()) != 0); }
    inline unsigned pos_block(unsigned p) { return p >> block_bits(); }
    inline unsigned pos_index(unsigned p) { return p & ((1<<block_bits())-1); }
    inline uint64_t pos_bit(unsigned p) { return 1ull << pos_index(p); }
  };

  // TODO: Factor all this stuff out
  namespace B64 {
    inline unsigned block_bits(void) { return 6; }
    inline unsigned block_size(void) { return 1 << block_bits(); }
    inline uint64_t block_mask(void) { return block_size()-1; }
    inline unsigned num_blocks(unsigned sz) { return (sz >> block_bits()) + ((sz & block_mask()) != 0); }
    inline unsigned pos_block(unsigned p) { return p >> block_bits(); }
    inline unsigned pos_index(unsigned p) { return p & ((1<<block_bits())-1); }
    inline uint64_t pos_bit(unsigned p) { return 1ull << pos_index(p); }

    static void Fill_BV(uint64_t* start, unsigned sz) {
      memset(start, -1, sizeof(uint64_t) * req_words(sz));
      if(mask(sz))
        start[base(sz)] &= bit(sz)-1;
    }

    template<class F>
    inline void Iter_BV(uint64_t* b, uint64_t* e, F f, int base = 0) {
      for(; b != e; ++b) {
        uint64_t mask(*b);
        while(mask) {
          unsigned offset(__builtin_ctzll(mask));
          mask &= (mask-1);
          f(base + offset);
        }
        base += 64;
      }
    }
    template<class F>
    inline bool Forall_BV(uint64_t* b, uint64_t* e, F f, int base = 0) {
      for(; b != e; ++b) {
        uint64_t mask(*b);
        while(mask) {
          unsigned offset(__builtin_ctzll(mask));
          mask &= (mask-1);
          if(!f(base + offset))
            return false;
        }
        base += 64;
      }
      return true;
    }
  };
};

#endif
