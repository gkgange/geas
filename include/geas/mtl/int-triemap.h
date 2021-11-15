#ifndef __GREYLIB_BIT_TRIEMAP_H__
#define __GREYLIB_BIT_TRIEMAP_H__
#include <cstdlib>
#include <cassert>
#include <geas/utils/cast.h>
#include <geas/mtl/bit-flag.h>

class UIntOps {
public:
  static uint64_t to_uint(uint64_t t) { return t; }
  static uint64_t from_uint(uint64_t t) { return t; }
};

class IntOps {
public:
  enum { mask = 1<<31 };
  static unsigned int to_uint(int t) { return ((unsigned int) t)^mask; }
  static int from_uint(unsigned int t) { return (int) (t^mask); }
};

class FloatOps {
  enum { mask = 1<<31 };
public:
  static unsigned int to_uint(float t)
  {
    int t_int = cast::conv<int, float>(t);
//    int t_int = *(reinterpret_cast<int*>(&t));
    if(t_int < 0)
      t_int = 0x80000000 - t_int;
    return mask^(t_int);
  }

  static float from_uint(unsigned int t)
  {
    int t_int = (int) (t^mask);
    if(t_int < 0)
      t_int = 0x80000000 - t_int;
    // return *(reinterpret_cast<float*>(&t_int));
    return cast::conv<float, int>(t_int);
  }
};

template<class Key, class Val, class Ops>
class uint64_triemap {
  typedef uint64_t elt_t;
private:
  uint64_triemap(uint64_triemap<Key, Val, Ops>& o)
    : root(nullptr) { }
  uint64_triemap& operator=(uint64_triemap<Key,Val,Ops>& o) {
    return *this;
  }
protected:
  // Internal and leaf nodes
  typedef struct {
    uint64_t mask;
    void* left;
    void* right;
  } node_t;

public:
  class ref_t {
  public:
    ref_t(const Key& _key, const Val& _val)
      : key(_key), value(_val)
    { }
    Key key;
    Val value;
  };

  class leaf_t {
  public:
    leaf_t(const Key& _elt, const Val& _val, leaf_t* _prev, leaf_t* _next)
      : ref(_elt, _val), prev(_prev), next(_next)
    { }
    ref_t ref;
    leaf_t* prev;
    leaf_t* next;
  };

  class iterator {
  public:
    iterator(leaf_t* _l)
      : l(_l)
    { } 

    iterator& operator++(void) {
      l = l->next; return *this;
    }
    iterator& operator--(void) {
      l = l->prev; return *this;
    }
    ref_t& operator*(void) const {
      return l->ref;
    }
    bool operator!=(const iterator& o) const {
      return l != o.l;
    }
    operator bool() {
      return l != NULL;
    }
  protected:
    leaf_t* l;
  };

  uint64_triemap(void)
    : root(NULL), head(NULL), tail(NULL)
  { } 

  uint64_triemap(uint64_triemap<Key, Val, Ops>&& o)
    : root(o.root), head(o.head), tail(o.tail) {
      o.root = nullptr;
      o.head = o.tail = nullptr;
  }

  uint64_triemap& operator=(uint64_triemap<Key, Val, Ops>&& o) {
    root = o.root; o.root = nullptr;
    head = o.head; o.head = nullptr;
    tail = o.tail; o.tail = nullptr;
    return *this;
  }

  ~uint64_triemap()
  {
    if(root)
      free_node(root);
  }

  iterator add(const Key& key, const Val& v) {
    if(!root)
    {
      root = make_leaf(key, v, NULL, NULL);
      head = tail = (leaf_t*) root;
      return head;
    }

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Already in the set
    if(leaf->ref.key == key)
    {
      leaf->ref.value = v;
      return leaf;
    }

//    unsigned int mask = get_mask(e^(leaf->ref.key));
    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    leaf_t* prev;
    leaf_t* next; 
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      prev = ((leaf_t*) adj_node);
      next = prev->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      next = ((leaf_t*) adj_node);
      prev = next->prev;
    }
    leaf_t* fresh_leaf = new leaf_t(key, v, prev, next);

    // Fix up the linked list
    if(fresh_leaf->prev)
      fresh_leaf->prev->next = fresh_leaf;
    if(fresh_leaf->next)
      fresh_leaf->next->prev = fresh_leaf;

    if(head == next)
      head = fresh_leaf;
    if(tail == prev)
      tail = fresh_leaf;

    void* fresh_node = make_node(mask,
      out_dir ? node : (void*) fresh_leaf,
      out_dir ? (void*) fresh_leaf : node);
    if(p == NULL)
      root = fresh_node;
    else
      (*p) = fresh_node;

    return fresh_leaf;
  }

  template<class Construct>
  Val find_or_add(Construct& construct, const Key& key) {
    if(!root)
    {
      root = make_leaf(key, construct(key), NULL, NULL);
      head = tail = (leaf_t*) root;
      return head->ref.value;
    }

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Already in the set
    if(leaf->ref.key == key)
    {
      return leaf->ref.value;
    }

    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    leaf_t* prev;
    leaf_t* next; 
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      prev = ((leaf_t*) adj_node);
      next = prev->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      next = ((leaf_t*) adj_node);
      prev = next->prev;
    }
    leaf_t* fresh_leaf = new leaf_t(key, construct(prev->ref.value, key), prev, next);

    // Fix up the linked list
    if(fresh_leaf->prev)
      fresh_leaf->prev->next = fresh_leaf;
    if(fresh_leaf->next)
      fresh_leaf->next->prev = fresh_leaf;

    if(head == next)
      head = fresh_leaf;
    if(tail == prev)
      tail = fresh_leaf;

    void* fresh_node = make_node(mask,
      out_dir ? node : (void*) fresh_leaf,
      out_dir ? (void*) fresh_leaf : node);
    if(p == NULL)
      root = fresh_node;
    else
      (*p) = fresh_node;

    return fresh_leaf->ref.value;
  }

  iterator lower_bound(const Key& key) {
    if(root == NULL)
      return NULL;

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Exact value present.
    if(leaf->ref.key == key)
    {
      return leaf;
    }

    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    // void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      // p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      return ((leaf_t*) adj_node)->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      return ((leaf_t*) adj_node);
    }
  }

  iterator upper_bound(const Key& key) {
    if(root == NULL)
      return NULL;

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Exact value present.
    if(leaf->ref.key == key)
    {
      return leaf->next;
    }

    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    // void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      // p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      return ((leaf_t*) adj_node)->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      return ((leaf_t*) adj_node);
    }
  }


  void rem(elt_t e)
  {
    if(root == NULL)
      return;

    void* p = root;
    node_t* q = NULL;

    void** whereq = NULL;
    void** wherep = &(root);
    uint64_t dir;

    while(check_flag(p))
    {
      whereq = wherep;
      q = clear_flag((node_t*) p);
      dir = e&(q->mask);
      wherep = dir ? &(q->right) : &(q->left);
      p = *wherep;
    }

    // If value not in the trie, terminate
    leaf_t* leaf((leaf_t*) p);
    if(e != leaf->ref.key)
      return;
    
    // Disconnect the leaf, then free it.
    if(leaf->prev)
    {
      leaf->prev->next = leaf->next;
    } else {
      head = leaf->next;
    }
    if(leaf->next)
    {
      leaf->next->prev = leaf->prev;
    } else {
      tail = leaf->prev;
    }
    delete leaf;

    // Collapse the last decision.
    if(!whereq)
    {
      root = NULL;
      return;
    }
    (*whereq) = dir ? q->left : q->right;
    delete q;
  }

  bool mem(elt_t e) {
    if(root == NULL)
      return false;

    leaf_t* leaf = locate(e);
    return (e == leaf->elt);
  }

  iterator find(const elt_t& e) const {
    if(root == NULL)
      return NULL;

    leaf_t* leaf = locate(e);
    return (e == leaf->ref.key) ? leaf : NULL;
  }

  iterator begin(void) const { return head; }
  iterator end(void) const { return NULL; }
protected:
  void free_node(void* ptr)
  {
    if(check_flag(ptr))
    {
      node_t* node_ptr(clear_flag((node_t*) ptr));
      free_node(node_ptr->left);
      free_node(node_ptr->right);
      delete node_ptr;
    } else {
      leaf_t* leaf_ptr((leaf_t*) ptr);
      delete leaf_ptr;
    }
  }
  void* make_node(uint64_t mask, void* left, void* right)
  {
    node_t* ptr = new node_t;
    ptr->mask = mask;
    ptr->left = left;
    ptr->right = right;
    
    return set_flag(ptr);
  }

  void* make_leaf(elt_t e, const Val& v, leaf_t* prev, leaf_t* next)
  {
    return (void*) (new leaf_t(e, v, prev, next));
  }

  // Extract the most significant 1-bit
  uint64_t get_mask(uint64_t x)
  {
    // Alternatively, use bit-smearing.
    // return (1<<(31-__builtin_clz(x)));
    static_assert(sizeof(uint64_t) == sizeof(unsigned long long),
      "uint64_trie: compiler intrinsic for wrong bit-width");
    return ((uint64_t) 1)<<(63-__builtin_clzll(x));
  }

  // Find the leaf where [elt] would reside
  leaf_t* locate(const elt_t& elt) const
  {
    if(root == NULL)
      return NULL;

    void* ptr = root;
    // While we're at an internal node
    while(check_flag(ptr))
    {
      node_t* node = clear_flag((node_t*) ptr);
      uint64_t dir = elt&node->mask;
      ptr = dir ? node->right : node->left;
    }
    return (leaf_t*) ptr;
  }

  void* root;
public:
  leaf_t* head;
  leaf_t* tail;
};

// Slightly different tradeoffs than the triemap.
class trieset {
  typedef uintptr_t elt_t;
  enum { KEY_BITS = 8*sizeof(elt_t) };
  
private:
  trieset(trieset& o) = delete;
  trieset& operator=(trieset& o) = delete;

protected:
  // Internal and leaf nodes
  struct node_t;
  
  class ref_t {
    ref_t(uintptr_t _p) : p(_p) { }
  public:
    ref_t(void) : p(0) { }
    static ref_t of_key(uint64_t x) { return ref_t((x<<1) | 1); }
    static ref_t of_node(node_t* ptr) { return reinterpret_cast<uintptr_t>(ptr); }
    static ref_t nil(void) { return ref_t(0); }

    bool is_nil(void) const { return !p; }
    bool is_branch(void) const { return ! (p&1); }
    bool is_key(void) const { return p&1; }

    uintptr_t key(void) const { return p>>1; }
    node_t* branch(void) const { return reinterpret_cast<node_t*>(p); }

    inline int dir(uintptr_t key) const {
      return ((key | branch()->mask)+1) >> (KEY_BITS-1);
    }
    inline ref_t child(uintptr_t key) const { return branch()->child[dir(key)]; }
    
    uintptr_t p;
  };

  struct node_t {
    uintptr_t mask;
    ref_t child[2];
  };

  static inline int _dir(node_t* b, elt_t e) {
    return ( (b->mask | e)+1 ) >> (KEY_BITS-1);
  }
 
public:
  // Two ways we can implement an iterator: stack-based, or successor based.
  class iterator {
  public:
    iterator(ref_t _root)
      : root(_root) {
      if(root.is_nil()) {
        key = UINTPTR_MAX;
      } else {
        ref_t ref = root;
        while(ref.is_branch())
          ref = ref.branch()->child[1];
        key = ref.key();
      }
    }
    iterator(ref_t _root, uintptr_t _key)
      : root(_root), key(_key) { }

    iterator& operator++(void) {
      // Navigate towards key, remember
      // the most recent right branch.
      ref_t curr = root;
      ref_t alt = ref_t::nil();

      while(curr.is_branch()) {
        int dir = curr.dir(key);
        if(dir)
          alt = curr.branch()->child[0];
        curr = curr.branch()->child[dir];
      }

      if(alt.is_nil()) {
        key = UINTPTR_MAX;
      } else {
        while(alt.is_branch()) {
          alt = alt.branch()->child[1];
        }
        key = alt.key();
      }
      return *this;
    }
    elt_t operator*(void) const {
      return key;
    }
    bool operator!=(const iterator& o) const {
      return key != o.key;
    }

    ref_t root;
    elt_t key;
  };

  trieset(void)
    : root(ref_t::nil())
  { } 

  trieset(trieset&& o)
    : root(o.root) {
    o.root = ref_t::nil();
  }

  trieset& operator=(trieset&& o) {
    root = o.root; o.root = ref_t::nil();
    return *this;
  }

  ~trieset()
  {
    if(!root.is_nil())
      free_node(root);
  }

  void remove(elt_t e)
  {
    if(root.is_nil())
      return;

    ref_t p = root;
    node_t* q = nullptr;

    ref_t* whereq = nullptr;
    ref_t* wherep = &(root);
    uint64_t dir;

    while(p.is_branch()) {
      whereq = wherep;
      q = p.branch();
      dir = _dir(q, e);
      wherep = q->child + dir;
      p = *wherep;
    }

    // If value not in the trie, terminate
    uintptr_t leaf = p.key();
    if(e != leaf)
      return;
    
    // Collapse the last decision.
    if(!whereq)
    {
      root = ref_t::nil();
      return;
    }
    (*whereq) = q->child[1 - dir];
    delete q;
  }

  bool mem(elt_t e) {
    if(root.is_nil())
      return false;

    elt_t leaf = locate(e);
    return (e == leaf);
  }

  void add(elt_t elt) {
    if(root.is_nil()) {
      root = ref_t::of_key(elt);
      return;
    }

    elt_t leaf = locate(elt);
    if(leaf == elt)
      return;

    // Actually the complement of the mask we'll
    // eventually add.
    elt_t delta = leaf ^ elt;

    ref_t* dest = &root;
    node_t* br = nullptr;
    while(dest->is_branch()) {
      br = dest->branch();
      // Check whether the next branch drops beneath the
      // first changed bit.
      if( (br->mask+1) & delta )
        break;
      dest = br->child + _dir(br, elt);
    }

    // Construct the new node.
    uintptr_t msb = get_msb(delta);
    // High child goes on the left.
    ref_t ref = (msb & elt) ? make_node(~msb, ref_t::of_key(elt), *dest)
      : make_node(~msb, *dest, ref_t::of_key(elt));
    *dest = ref;
  }

  iterator begin(void) const { return iterator(root); }
  iterator end(void) const { return iterator(root, UINTPTR_MAX); }
protected:
  void free_node(ref_t ref) {
    if(!ref.is_branch())
      return;

    node_t* ptr(ref.branch());
    free_node(ptr->child[0]);
    free_node(ptr->child[1]);
    delete ptr;
  }

  ref_t make_node(uint64_t mask, ref_t left, ref_t right)
  {
    node_t* ptr = new node_t;
    ptr->mask = mask;
    ptr->child[0] = left;
    ptr->child[1] = right;
    
    return ref_t::of_node(ptr);
  }

  // Extract the most significant 1-bit
  uint64_t get_msb(uint64_t x)
  {
    // Alternatively, use bit-smearing.
    // return (1<<(31-__builtin_clz(x)));
    static_assert(sizeof(uint64_t) == sizeof(unsigned long long),
      "uint64_trie: compiler intrinsic for wrong bit-width");
    return ((uint64_t) 1)<<(63-__builtin_clzll(x));
  }

  // Find the leaf where [elt] would reside
  elt_t locate(elt_t elt) const {
    assert(!root.is_nil());

    ref_t ref = root;
    // While we're at an internal node
    while(ref.is_branch()) {
      ref = ref.child(elt);
    }
    return ref.key();
  }

  ref_t root;
};

// Yet another *slightly* different trie variant.
// TODO: unify as many of these as is possible.
template<class V>
class triemap {
  typedef uintptr_t elt_t;
  enum { KEY_BITS = 8*sizeof(elt_t) };
  
private:
  // We take ownership of our nodes, so 
  triemap(triemap<V>& o) = delete;
  triemap& operator=(triemap<V>& o) = delete;

protected:
  // Internal and leaf nodes
  struct node_t;
  struct leaf_t;
  
  class ref_t {
    ref_t(uintptr_t _p) : p(_p) { }
  public:
    ref_t(void) : p(0) { }
    static ref_t of_leaf(leaf_t* ptr) { return reinterpret_cast<uintptr_t>(ptr) | 1; }
    static ref_t of_node(node_t* ptr) { return reinterpret_cast<uintptr_t>(ptr); }
    static ref_t nil(void) { return ref_t(0); }

    bool is_nil(void) const { return !p; }
    bool is_branch(void) const { return ! (p&1); }
    bool is_leaf(void) const { return p&1; }

    leaf_t* leaf(void) const { return reinterpret_cast<leaf_t*>(p & ~1ull); }
    node_t* branch(void) const { return reinterpret_cast<node_t*>(p); }

    inline int dir(uintptr_t key) const {
      return ((key | branch()->mask)+1) >> (KEY_BITS-1);
    }
    inline ref_t child(uintptr_t key) const { return branch()->child[dir(key)]; }
    
    uintptr_t p;
  };

  struct node_t {
    uintptr_t mask;
    ref_t child[2];
  };
  struct leaf_t {
    leaf_t(uint64_t _key, V _value) : key(_key), value(_value) { }
    uint64_t key;
    V value;
  };

  static inline int _dir(node_t* b, elt_t e) {
    return ( (b->mask | e)+1 ) >> (KEY_BITS-1);
  }
 
public:
  // Two ways we can implement an iterator: stack-based, or successor based.
  class iterator {
  public:
    iterator(ref_t _root)
      : root(_root) {
      if(root.is_nil()) {
        leaf = nullptr;
      } else {
        ref_t ref = root;
        while(ref.is_branch())
          ref = ref.branch()->child[1];
        leaf = ref.leaf();
      }
    }
    iterator(ref_t _root, leaf_t* _leaf)
      : root(_root), leaf(_leaf) { }

    iterator& operator++(void) {
      // Navigate towards key, remember
      // the most recent right branch.
      ref_t curr = root;
      ref_t alt = ref_t::nil();

      uint64_t key(leaf->key);

      while(curr.is_branch()) {
        int dir = curr.dir(key);
        if(dir)
          alt = curr.branch()->child[0];
        curr = curr.branch()->child[dir];
      }

      if(alt.is_nil()) {
        leaf = nullptr;
      } else {
        while(alt.is_branch()) {
          alt = alt.branch()->child[1];
        }
        leaf = alt.leaf();
      }
      return *this;
    }
    leaf_t* operator*(void) const {
      return leaf;
    }
    bool operator!=(const iterator& o) const {
      return leaf != o.leaf;
    }

    ref_t root;
    leaf_t* leaf;
  };

  triemap(void)
    : root(ref_t::nil())
  { } 

  triemap(triemap&& o)
    : root(o.root) {
    o.root = ref_t::nil();
  }

  triemap& operator=(triemap&& o) {
    root = o.root; o.root = ref_t::nil();
    return *this;
  }

  ~triemap()
  {
    if(!root.is_nil())
      free_node(root);
  }

  bool empty(void) const { return root.is_nil(); }

  void remove(elt_t e)
  {
    if(root.is_nil())
      return;

    ref_t p = root;
    node_t* q = nullptr;

    ref_t* whereq = nullptr;
    ref_t* wherep = &(root);
    uint64_t dir;

    while(p.is_branch()) {
      whereq = wherep;
      q = p.branch();
      dir = _dir(q, e);
      wherep = q->child + dir;
      p = *wherep;
    }

    // If value not in the trie, terminate
    leaf_t* leaf = p.leaf();
    if(e != leaf->key)
      return;

    delete leaf;
    // Collapse the last decision.
    if(!whereq)
    {
      root = ref_t::nil();
      return;
    }
    (*whereq) = q->child[1 - dir];
    delete q;
  }

  bool mem(elt_t e) const {
    if(root.is_nil())
      return false;

    leaf_t* leaf = locate(e);
    return (e == leaf->key);
  }

  V* find(elt_t elt) {
    if(root.is_nil())
      return nullptr;

    leaf_t* leaf = locate(elt);
    if(leaf->key != elt)
      return nullptr;
    return &(leaf->value);
  }

  void insert(elt_t elt, V val) {
    if(root.is_nil()) {
      leaf_t* new_leaf = new leaf_t(elt, val);
      root = ref_t::of_leaf(new_leaf);
      return;
    }

    leaf_t* leaf = locate(elt);
    if(leaf->key == elt) {
      leaf->value = val;
      return;
    }

    leaf_t* new_leaf = new leaf_t(elt, val);

    // Actually the complement of the mask we'll
    // eventually add.
    elt_t delta = leaf->key ^ elt;

    ref_t* dest = &root;
    node_t* br = nullptr;
    while(dest->is_branch()) {
      br = dest->branch();
      // Check whether the next branch drops beneath the
      // first changed bit.
      if( (br->mask+1) & delta )
        break;
      dest = br->child + _dir(br, elt);
    }

    // Construct the new node.
    uintptr_t msb = get_msb(delta);
    // High child goes on the left.
    ref_t ref = (msb & elt) ? make_node(~msb, ref_t::of_leaf(new_leaf), *dest)
      : make_node(~msb, *dest, ref_t::of_leaf(new_leaf));
    *dest = ref;
  }

  iterator begin(void) const { return iterator(root); }
  iterator end(void) const { return iterator(root, nullptr); }
protected:
  void free_node(ref_t ref) {
    if(!ref.is_branch())
      return;

    node_t* ptr(ref.branch());
    free_node(ptr->child[0]);
    free_node(ptr->child[1]);
    delete ptr;
  }

  ref_t make_node(uint64_t mask, ref_t left, ref_t right)
  {
    node_t* ptr = new node_t;
    ptr->mask = mask;
    ptr->child[0] = left;
    ptr->child[1] = right;
    
    return ref_t::of_node(ptr);
  }

  // Extract the most significant 1-bit
  uint64_t get_msb(uint64_t x)
  {
    // Alternatively, use bit-smearing.
    // return (1<<(31-__builtin_clz(x)));
    static_assert(sizeof(uint64_t) == sizeof(unsigned long long),
      "uint64_trie: compiler intrinsic for wrong bit-width");
    return ((uint64_t) 1)<<(63-__builtin_clzll(x));
  }

  // Find the leaf where [elt] would reside
  leaf_t* locate(elt_t elt) const {
    assert(!root.is_nil());

    ref_t ref = root;
    // While we're at an internal node
    while(ref.is_branch()) {
      ref = ref.child(elt);
    }
    return ref.leaf();
  }

  ref_t root;
};

#endif
