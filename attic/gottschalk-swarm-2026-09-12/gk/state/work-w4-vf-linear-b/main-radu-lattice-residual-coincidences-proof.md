---
rg: 2
id: radu-lattice-residual-coincidences-proof
kind: route
title: Push the pair to the residually finite quotient and measure the finite residual
target: radu-lattice-one-sided-pairs-need-residual-coincidences
requires:
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
  - one-sided-inverse-pairs-transfer-to-table-realizations
  - strict-pairs-transfer-to-table-realizations
  - sofic-groups-are-surjunctive
  - stable-finiteness-failure-refutes-surjunctivity
  - radu-bmw-coordinate-subgroups-are-sofic
artifacts:
  - research/artifacts/radu-lattice-anchored-linear-gadgets-2026-09-12.md
---

## Why sufficient

1. **Item 1** (Theorem 3.1). `Gamma_R / Gamma_0` is residually finite, so it is sofic and surjunctive,
   and its matrix algebras over `F_p` are directly finite by the contrapositive of
   `stable-finiteness-failure-refutes-surjunctivity`. The images of `A` and `B` are two-sided
   inverses, so the image of the defect is zero. A nonzero entry whose coefficients sum to zero on a
   coset has two support points in that coset.
2. **Item 2** (Corollary 3.2). Replacing `(A, B)` by `(u^(-1) A, B u)` centres the balls. The two
   points lie in `B_(r+s)`, so their difference has length at most `2(r+s)`, and every nontrivial
   element of `Gamma_0` has length at least eight.
3. **Item 3** (Theorem 1.2, Proposition 1.3). `iota(g) = g^(-1)` extends to an anti-automorphism.
   Elements supported in `B_1` are `iota`-fixed because the letters are involutions, so
   `A B = iota(B A) = 1`. Over `F_2`, the coefficient equations of `B A = 1` on the two-letter
   products, sorted by the square table re-derived from the relators, give the classification.
4. **Item 4** (Theorem 2.1). From each triple the substitutions `b = zaz`, `a = zbz`, `c = yby`,
   `b = ycy`, `z = cxc` and `x = czc` generate all six letters. A set failing the criterion lies in
   `P_xz`, `P_y`, `V` or `<a,x,y>`. These are sofic by `radu-bmw-coordinate-subgroups-are-sofic`, by
   virtual freeness, and by amenability.
5. **Screen.** Apply Corollary 2 of `strict-pairs-transfer-to-table-realizations` to
   `H -> H / (H ∩ Gamma_0)`, a subgroup of a residually finite group (Section 5).
