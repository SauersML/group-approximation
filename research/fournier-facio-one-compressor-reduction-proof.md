---
rg: 2
id: fournier-facio-one-compressor-reduction-proof
kind: route
title: Apply the directed-union-by-cyclic theorem to the first Fournier--Facio compressor
target: fournier-facio-one-compressor-subgroup-reduces-to-gamma
requires:
  - compressor-subgroup-is-directed-union-by-cyclic
  - fournier-facio-group-contains-simple-wreath-shift
---

Every `J_k = t_1^k J t_1^-k`, with `J = t_1^-1 pi(S) t_1` and `pi(S) <= Gamma`,
is a word in `Gamma` and `t_1`.  So is everything built from them in the
wreath-shift node, and the commutant-shift computations use only those
relations.  Clause (W7) at `n = 1` gives `Gamma >= J_1 x t_1 Gamma t_1^-1`
with `J_1 = pi(S) != 1`, so the compression is proper.  `Gamma` is finitely
generated because it has property (T).  The general theorem then gives
clauses 2 and 3.  For `t_2` the same theorem applies verbatim.
