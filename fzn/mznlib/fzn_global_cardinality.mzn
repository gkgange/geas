predicate fzn_global_cardinality(array[int] of var int: x,
                             array[int] of int: cover,
                             array[int] of var int: count) =
  forall (i in index_set(cover)) (
    count[i] = sum (j in index_set(x)) (bool2int(x[j] = cover[i]))
  );

predicate fzn_global_cardinality(array[int] of var int: x,
                             array[int] of int: cover,
                             array[int] of int: count);
