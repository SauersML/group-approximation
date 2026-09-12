---
rg: 2
id: leavitt-tensor-powers-are-not-left-coherent
kind: claim
title: No tensor power of L_k(1,2) with at least two factors is left or right coherent
invalidates: [leavitt-tensor-powers-k-theory-via-coherence, prime-field-leavitt-powers-k-theory-via-coherence]
distinct_from:
  leavitt-tensor-powers-are-left-coherent: that asserts coherence of L^(⊗d) for d >= 2; this refutes it with an explicit principal left ideal that is not finitely presented.
  leavitt-tensor-global-dimension-bound: that bounds the global dimension of L^(⊗d) by d; this shows the rings are not coherent, so the finite global dimension does not make them regular coherent.
---

**ESTABLISHED (derivation).** Let `k` be a field and `L = L_k(1,2)`, with
generators `x_1, x_2` of degree `1` and `y_1, y_2` of degree `−1`, and relations
`y_i x_j = δ_ij`, `x_1 y_1 + x_2 y_2 = 1`. For every `d >= 2` the algebra
`L^(⊗d)` is neither left nor right coherent.

**Witness for `A = L ⊗ L`.**
- `u = x_1 ⊗ y_1 + x_2 ⊗ y_2` is a unit, with inverse `y_1 ⊗ x_1 + y_2 ⊗ x_2`.
- `e = x_1 y_1 ⊗ 1` is an idempotent.
- The principal left ideal `A (1 − u) e` is not finitely presented.
  Equivalently, `A (1 − u) ∩ A (1 − e)` is not finitely generated.

For `d > 2` the same elements tensored with `1` are a witness.

**The mechanism.** The total-degree-zero ring `T = ⊕_n L_n ⊗ L_(−n)` is the
algebraic Bernoulli crossed product `(⊗'_(Z) M_2(k)) ⋊ Z`, with `u` acting as
the shift. `A` is strongly graded over `T`, so coherence of `A` would give
coherence of `T`. In `T`, a left annihilator of `(1 − u) e` constant along a
run of `ℓ` ones in a two-sided binary sequence has width `ℓ + 1`. Finitely many
annihilators, and their left multiples, only reach runs of bounded length.
Route: `leavitt-tensor-powers-not-left-coherent-proof`.

**Consequences.**
- `leavitt-tensor-powers-are-left-coherent` is false for every field and every
  `d >= 2`. The routes `leavitt-tensor-powers-k-theory-via-coherence` and
  `prime-field-leavitt-powers-k-theory-via-coherence` are dead.
- Attempt 2 of that node asked whether graded coherence passes to ungraded
  coherence for `Z^d`-gradings over an ultramatricial base. It does not, even
  for `Z`: `T` is strongly `Z`-graded over the von Neumann regular ring
  `⊗'_(Z) M_2(k)`, so it is graded von Neumann regular, and it is not coherent.
  The same argument, with points in place of vectors, shows that the crossed
  product `C(X, k) ⋊ Z` of the full two-shift on `X = {1,2}^Z` is not coherent.
- What stays open: `K_1 = K_2 = 0` for `L^(⊗d)` with `d >= 3`
  (`leavitt-tensor-powers-have-trivial-k-theory` and its prime-field twin).
  `regular-coherent-coefficients-kill-leavitt-tensor-k-theory` no longer applies
  to `R = L^(⊗(d−1))`. Waldhausen's Nil vanishing needs coherence, and Vogel's
  extension to non-coherent regular rings is a conjecture (Bihler
  arXiv:math/0612569). So a proof must compute the twisted Nil groups of
  Attempt 4 there directly.
