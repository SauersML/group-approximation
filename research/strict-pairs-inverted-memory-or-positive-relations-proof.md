---
rg: 2
id: strict-pairs-inverted-memory-or-positive-relations-proof
kind: route
title: Peel privately read sites to a permutive normal form, then solve any finite pattern along the acyclic dependency order
target: strict-pairs-need-inverted-memory-or-positive-memory-relations
requires: []
---

Assume case 1 fails: `1 ∉ sM` for every `s` in `S \ {1}`. We show case 2 holds.

**Step 1 (peeling).** Let `N ⊆ M` contain `1`, and suppose `mu` depends only on the coordinates
in `N`. Put `E' = (N \ {1}) ∩ ⋃_(s ≠ 1) sN` and `N' = {1} ∪ E'`. Then for each `c` in `A^(E')`
there is a permutation `f_c` of `A` with `mu(w) = f_(w|E')(w_1)`; in particular `mu` depends
only on `N'`.
- *Private sites.* For `s != 1`, `tau(x)(s)` reads `x` on `sN`. By case 1, `1 ∉ sN`, and by
  definition of `E'`, `sN ∩ N ⊆ E'`. So the sites of `N \ E'`, site `1` among them, are read by
  no relay `s != 1`.
- *The decoder at site 1.* Fix `x` off `N \ E'`, and let `w` in `A^N` range over the assignments
  with `w|E' = c`. The relay values at `s != 1` stay fixed, and
  `x(1) = nu(mu(w), (fixed relay values))`. So `mu(w)` determines `w_1`.
- *Counting.* `w_1` takes all `|A|` values and `mu(w)` at most `|A|`, so `w -> mu(w)` is a
  bijective function of `w_1` on these assignments. It does not depend on the other sites of
  `N \ E'`.

**Step 2 (normal form).** Start with `N = M` and apply Step 1 until `N` stops shrinking. The fixed
point `N* = {1} ∪ E` has `E ⊆ ⋃_(s ≠ 1) sN*` and `tau(x)(g) = f_(x|gE)(x(g))`. If `E` is empty,
`tau(x) = f o x` is bijective; so `E` is nonempty.

**Step 3 (a positive relation in `E`).** Suppose no product of elements of `E` equals `1`. On
`G`, draw an edge `g -> ge` for each `e` in `E`. A directed cycle
`g -> g e_1 -> ... -> g e_1 ... e_k = g` would give `e_1 ... e_k = 1`, so the digraph is acyclic.
Let `Omega` be finite and `p` in `A^Omega`.
- Order `Omega` so that every `w` comes after its out-neighbours in `Omega`; a finite acyclic
  digraph has such an order.
- Fix `x` arbitrarily off `Omega`, and define `x(w)` along the order by
  `x(w) = f_(x|wE)^(-1)(p(w))`. Every site of `wE` is off `Omega` or already defined.
- Then `tau(x)|Omega = p`.

So every finite pattern is displayed. The image of `tau` is closed, since `tau` is continuous on
a compact space, and it is dense, so `tau` is surjective. This contradicts the hypothesis, so some
product of elements of `E` equals `1`.

**Step 4 (a positive relation in `S \ {1}`).** Each `e` in `E` is `s e'` with `s` in `S \ {1}`
and `e'` in `N*`. Follow `e -> e' -> e'' -> ...`.
- If the chain reaches `1`, then `e` is a product of elements of `S \ {1}`.
- Otherwise it stays in the finite set `E` and repeats a term, `e_i = s_i ... s_(j-1) e_i`, which
  gives a product of elements of `S \ {1}` equal to `1`.

If every chain reaches `1`, substitute these products into the relation of Step 3. Either way some
product of elements of `S \ {1}` equals `1`, and case 2 holds.

**Corollary.** With `M \ {1}` and `S \ {1}` inside a subsemigroup `P` avoiding `1`, case 1 gives
`1 = sm ∈ P` and case 2 gives `1 = e_1 ... e_k ∈ P`. Both are impossible, so `tau` is surjective.

The argument uses no finite model and no property of `G`.
