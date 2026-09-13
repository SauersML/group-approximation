---
rg: 2
id: atiyah-base-change-in-transcendence-degree-one-under-det
kind: claim
title: Under the determinant conjecture, Strong Atiyah over the algebraic numbers extends to every coefficient field of transcendence degree one, with the center and algebraic eigenvalue conjectures over Qbar
distinct_from:
  determinant-conjecture-gives-one-variable-atiyah-base-change: that proves the purely transcendental case Qbar(z) through a resultant identity; this extends it to algebraic extensions of Qbar(z) by continuity along curves, and adds the eigenvalue and center conjectures over Qbar.
  determinant-conjecture-gives-full-atiyah-base-change: that is the open statement for all complex coefficients; this is its established transcendence-degree-one case.
  galois-invariance-implies-algebraic-eigenvalues: that derives algebraic eigenvalues for matrices over the group algebra from full Galois invariance; this derives them for matrices over the division closure from the determinant conjecture and Strong Atiyah over Qbar.
artifacts:
  - research/artifacts/atiyah-transcendence-degree-one-base-change-2026-09-13.md
  - research/artifacts/atiyah-one-variable-base-change-2026-09-12.md
---

**ESTABLISHED (unreviewed)** by [[atiyah-transcendence-degree-one-proof]].

Let `G` be torsion-free and satisfy Strong Atiyah over `Qbar` and Lueck's
determinant conjecture, and put `D = D_(Qbar[G])`.

1. **Transcendence degree one.** For every field `F ⊂ C` with
   `trdeg_(Qbar) F <= 1`, every matrix over `F[G]` has integral von Neumann
   kernel dimension, and it is invariant under automorphisms of `C` fixing
   `Qbar`.
2. **Strong algebraic eigenvalue conjecture over `Qbar`.** Every eigenvalue of
   every square matrix over `D` is algebraic.
3. **Center conjecture over `Qbar`.** `D ∩ C = Qbar`.

Items 2 and 3 are two of the four conjectures listed by Jaikin-Zapirain--Lopez-Alvarez
(arXiv:1810.12135v4, p. 3), which proved them for locally indicable groups.
Item 1 contains the independence conjecture for these fields.

**Mechanism for item 1.**
* Write `F = Qbar(C)` for a smooth affine curve `C`, and choose a finite map
  `x: C -> A^1`.
* Restriction of scalars along `Qbar[x] ⊂ Qbar[C]` gives a one-variable family
  whose kernel at an unramified `z` is the sum of `k(P) = dim ker M(P)` over the
  fibre. By `determinant-conjecture-gives-one-variable-atiyah-base-change`, that
  sum is constant off finitely many algebraic `z`.
* `k` is upper semicontinuous at every point. Constant fibre sums make it lower
  semicontinuous as well, so `k` is continuous on `C` minus finitely many points.
* `k` is an integer at the dense algebraic points, so it is a constant integer on
  that connected set, and every transcendental point carries the same value.

**Mechanism for items 2 and 3.** A transcendental eigenvalue of `U B^-1 V` over
`D` is a jump of the family `[[B, V], [U, x I]]` over `Qbar[G][x]`. The one-variable
theorem excludes such jumps. A transcendental element of `D ∩ C` is such an
eigenvalue of a `1 x 1` matrix.

**What remains.** Coefficient fields of transcendence degree at least two:
`determinant-conjecture-gives-full-atiyah-base-change`.

**Model test.** For `G = Z/2` the family `x(1+s)/2` gives kernel `1/2` at every
`z != 0`, so the torsion-free and Strong Atiyah hypotheses are needed. For sofic
groups Jaikin-Zapirain's base change gives item 1 directly, which is consistent.
