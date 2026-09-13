---
rg: 2
id: pure-braid-product-projections-obstruct-bnsr-invariants-proof
kind: route
title: Layered sections make P_n -> prod H_{A_i} split, and the product has nonzero Euler characteristic in dimension D
target: pure-braid-product-projections-obstruct-bnsr-invariants
requires:
  - split-quotient-euler-obstruction-to-bnsr-invariants
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

Artifact, Section A.

1. Layered sections. For `A <= [n]`, `(phi_A, phi_{A^c}): P_n -> P_A x P_{A^c}` is
   split. Push the strands of `A` into the upper half-plane and the others into
   the lower half-plane. Pure braids of the two families, supported in disjoint
   open half-planes, commute. Erasing strands restricts to the projections, up
   to the homotopy equivalence `Conf_k(half-plane) -> Conf_k(C)`. Iterating
   shows `(phi_{A_1}, ..., phi_{A_r}): P_n -> prod_i P_{A_i}` is split.
2. Each `P_{A_i} = H_{A_i} x Z` splits (full twist), so `P_n -> Q = prod_i H_{A_i}` is
   split. `Q` has a finite classifying space of dimension `D` and Euler
   characteristic `prod_i (-1)^{|A_i|} (|A_i| - 2)! != 0` (artifact
   `zp-pure-braid-bnsr-top-range-2026-09-13.md`, Lemma L).
3. The block-supported zero-sum `chi` is `psi o pi` for a nonzero character
   `psi` of `Q`, so `split-quotient-euler-obstruction-to-bnsr-invariants` gives
   `[chi] notin Sigma^D(P_n)`.
