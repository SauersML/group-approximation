---
rg: 2
id: raag-virtual-fp-n-kernel-forces-acyclic-flag-complex
kind: claim
title: If a finite-index subgroup of a right-angled Artin group maps onto Z with kernel of type FP_n, the flag complex is (n-1)-acyclic over the same coefficients
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md
distinct_from:
  raag-virtual-fn-kernel-implies-raag-fn-kernel: that is Zaremsky's conjecture with homotopical finiteness F_n in hypothesis and conclusion; this is the homological statement about the flag complex, which settles the FP_n form of the conjecture and leaves only the fundamental group of L.
---

Let `L` be a finite flag complex, `H ≤ A_L` of finite index, and `n ≥ 1`.

1. If `F` is a field and some epimorphism `H → Z` has kernel of type `FP_n(F)`, then
   `H̃_j(L; F) = 0` for all `j ≤ n − 1`.
2. If some epimorphism `H → Z` has kernel of type `FP_n(Z)`, then `H̃_j(L; Z) = 0` for all
   `j ≤ n − 1`.

Consequences, through the Bestvina--Brady theorem (`BB_L` is of type `FP_n(R)` iff `L` is
`(n−1)`-acyclic over `R`; statement recalled and not yet re-read from the source): `A_L`
itself maps onto `Z` with a kernel of type `FP_n(F)`, resp. `FP_n(Z)`. This is the homological
form of Zaremsky's Problem 1.19, over every field and over `Z`. A counterexample to the
conjecture itself must have `n ≥ 2` and `L` with `H_1(L; Z) = 0` but `π_1(L) ≠ 1`.

Proof: bi-orderability of right-angled Artin groups (Duchamp--Krob, Duchamp--Thibon, 1992),
then compare `raag-skew-field-betti-numbers-of-finite-index-subgroups` with
`bi-orderable-fp-n-fibre-kills-malcev-neumann-homology` for `D = F((H,<))`; over `Z`, use every
field and universal coefficients. Artifact part 1, Theorem 3.

UNREVIEWED as of 2026-09-13 (review requested from z-verify-topology).
