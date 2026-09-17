---
rg: 2
id: rips-segev-witness-pairs-carry-no-zero-divisors-proof
kind: route
title: Rank-one coefficient patterns factor into non-zero-divisors, and a clean product square forces rank one
target: rips-segev-witness-pairs-carry-no-zero-divisors
requires: []
---

Throughout, `G` is torsion-free and `k` is a field.  For `gamma in k[G]`, `gamma(g)` denotes the coefficient of
`g`.

**Lemma 0 (non-zero-divisors from cyclic subgroups).**  Let `a != 1` and `p in k[<a>]`, `p != 0`.  Then
`gamma p = 0` or `p gamma = 0` forces `gamma = 0`.

*Proof.*
- Since `G` is torsion-free, `<a> ≅ Z` and `k[<a>]` is a Laurent polynomial ring, hence a domain.
- As a right `k[<a>]`-module, `k[G]` is free on a set `T` of left coset representatives:
  `gamma = sum_{t in T} t gamma_t` with `gamma_t in k[<a>]`.  Then `gamma p = sum_t t (gamma_t p)`, and
  `gamma p = 0` forces every `gamma_t p = 0`, hence every `gamma_t = 0`.
- The case `p gamma = 0` uses right cosets in the same way. ∎

**(T1).**
- *Factorization.*  If `b_1 b_ab = b_a b_b` with `b_1 != 0`, put `x = b_a/b_1` and `y = b_b/b_1`.  Then
  `b_1 (1 + x a)(1 + y b) = b_1 + b_a a + b_b b + b_1 x y ab`, and `b_1 x y = b_a b_b / b_1 = b_ab`.
- *Non-vanishing.*  Suppose `alpha beta = 0`.  Then `(alpha (1+xa)) (1+yb) = 0`.  By Lemma 0 with `p = 1+yb`
  (and `b != 1`), `alpha(1+xa) = 0`.  By Lemma 0 again (`a != 1`), `alpha = 0`.
- *Over `F_2`.*  All nonzero coefficients equal `1`, so the rank-one condition holds.  The translate statement
  follows because left multiplication by a group element is a unit.
- *Product supports over `F_2`.*  If `supp beta = S T` with all products distinct, then `(sum S)(sum T)` has
  coefficient `1` at each product and `0` elsewhere, so it equals `beta`.  Suppose `beta` is a zero divisor of
  minimal support size and `alpha beta = 0` with `alpha != 0`.
  - If `alpha (sum S) = 0`, then `sum S` is a zero divisor with support `|S| < |S||T|`.
  - Otherwise `alpha (sum S) != 0` annihilates `sum T`, so `sum T` is a zero divisor with support `|T| < |S||T|`.

  Right zero divisors are handled the same way.  In both cases minimality is contradicted.  (Left and right
  zero divisors coincide as a class, via the involution `g -> g^{-1}`.) ∎

**(T2).**  Let `alpha beta = 0`, `h, ha in supp alpha`, and suppose the only expressions of `ha` and `hab` as
products in `supp(alpha) supp(beta)` are `ha = (ha) 1 = h a` and `hab = (ha) b = h (ab)`.
- Reading the coefficients of `ha` and `hab` in `alpha beta = 0`:

  ```text
  alpha(ha) b_1  + alpha(h) b_a  = 0,
  alpha(ha) b_b  + alpha(h) b_ab = 0.
  ```

- The vector `(alpha(ha), alpha(h))` has both entries nonzero and lies in the kernel of the matrix
  `[[b_1, b_a], [b_b, b_ab]]`.  So its determinant vanishes: `b_1 b_ab = b_a b_b`.
- By (T1), `alpha beta != 0`, a contradiction. ∎

**(T3).**
- *Positions.*  In Steenbock's construction `A = sqcup_i {v_il = c_i a^l : 0 <= l < C_i}` and `B = {1,a,b,ab}`.
  The products sit at `v_il 1 = v_il`, `v_il a = v_{i,l+1}`, `v_il b = w_il` and `v_il ab = w_{i,l+1}`.  So
  inside line `i`, for `1 <= l <= C_i - 1`, the vertex `v_il` carries the products `v_il 1` and `v_{i,l-1} a`,
  and `w_il` carries `v_il b` and `v_{i,l-1} ab`.
- *Extra products.*  Step 1 identifies each `w`-endpoint (`l = 0` or `l = C_i`) with some `v_jI`, which adds
  products at `v_jI`.  Step 2 identifies each remaining `v`-endpoint with an interior `w_lO`, which adds products
  at `w_lO`.  Steps 3--4 identify no vertices of `Theta'` carrying products; this is part of (EE).  Interior
  positions are never sources of a gluing.
- *A free index is a clean square.*  Under (EE), at a free index `(i,l)` the elements `v_il` and `w_il` of
  `G(Gamma)` have exactly the two expressions listed above.  With `h = v_{i,l-1}` and `ha = v_il`, both in
  `A = supp alpha`, the hypotheses of (T2) hold, so no pair with `supp alpha = A` and `supp beta = B` has
  `alpha beta = 0`.
- *Counting.*  Steps 1 and 2 use `2K` targets each, so at most `4K` interior indices are non-free.  Hence
  `sum_i (C_i - 1) > 4K` gives a free index. ∎

**Sufficient condition for (EE).**
- Let `Gamma^+` be obtained by Steps 1, 2 and 4 while omitting Step 3 (the deletion of degree-one `b`-edges).
  Deleting degree-one edges does not change the presented group, so `G(Gamma^+) = G(Gamma)`.
- Every product `x y` with `x in A` and `y in B` is the terminal vertex of the path `p_x p_y` from `*` in
  `Gamma^+`.  If `Gamma^+` has a reduced labeling satisfying `Gr'_*(1/6)`, Steenbock's Theorem "gi" says `Gamma^+`
  injects into the Cayley graph of `G(Gamma^+)`.  Two products are then equal in the group exactly when their
  vertices of `Gamma^+` coincide, and that is (EE).
- Whether Steenbock's explicit families satisfy this for `Gamma^+` rather than `Gamma` is not checked here.
  Re-attaching the hanging edges can lengthen pieces by at most one letter at each end.

**Generalization.**  Let `beta = P + Q` with `P = 1 + sum_j y_j b_j` and `Q = a (x + sum_j z_j b_j)`.
- The clean-square computation at a free index of line `i` along the pair `(b_j, ab_j)` gives `z_j = x y_j`.
  So `beta = (1 + x a) P`.
- By Lemma 0, `alpha beta = 0` forces `alpha (1+xa) != 0` to annihilate `P`.  This is a strict reduction of
  support, from `2d` to `d`, and not a contradiction.

**Pattern solutions are genuine.**  Every gluing of Steps 1--2 (and the folding of Step 4) identifies vertices
that represent equal elements of `G(Gamma)`: the vertex reached from `*` by `p_x p_y` represents `xy`.  Hence the
partition of `A B` by equality in `G(Gamma)` is coarser than the pattern partition.  The coefficient of `g` in
`alpha beta` is the sum, over the pattern classes lying over `g`, of the pattern coefficients.  A pattern kernel
vector therefore gives `alpha beta = 0` in `k[G(Gamma)]`, provided the pushforward of `alpha` along `A -> G(Gamma)`
is nonzero (for instance when `A` injects).  With `beta` factorizable, (T1) then forces torsion, `a = 1` or `b = 1`
in `G(Gamma)`, or a vanishing pushforward. ∎

**Computation.**  `experiments/rips-segev-coefficient-rigidity-2026-09-17/rs_witness_nullspace.py` builds the
encoded pattern model for random Steps 1--2 gluings and computes kernels of `alpha -> alpha beta` over `F_p`.
The commands and outputs are in `results.txt`.
- The calibration in the finite abelian groups `Z/n x Z/m` finds annihilated `beta`, as it must with torsion.
- No full-support non-factorizable kernel vector appears in any graph with a free index, matching (T2).
- Such vectors do appear over `F_5` and `F_3` in gluings without free indices, so the hypothesis cannot be dropped
  at pattern level.
- Roughly a quarter of the random gluings have a nonzero pattern kernel for a factorizable `beta`.  By the remark
  above, none of those gluings yields a torsion-free group in which `A` embeds and `b != 1`.
