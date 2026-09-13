---
rg: 2
id: raag-virtual-fp-n-kernel-forces-acyclic-flag-complex-proof
kind: route
title: Malcev--Neumann coefficients kill low homology of the fibred subgroup, while the Salvetti computation says it is index times the reduced homology of L
target: raag-virtual-fp-n-kernel-forces-acyclic-flag-complex
requires:
  - raag-skew-field-betti-numbers-of-finite-index-subgroups
  - bi-orderable-fp-n-fibre-kills-malcev-neumann-homology
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part1.md
---

`L ≠ ∅`, since the trivial group has no epimorphism onto `Z`. Right-angled Artin groups
are bi-orderable (G. Duchamp and D. Krob, Semigroup Forum 45 (1992); G. Duchamp and
J.-Y. Thibon, Internat. J. Algebra Comput. 2 (1992)), so `H` inherits a bi-invariant order.
Put `D = F((H, <))`.

Field case: by `bi-orderable-fp-n-fibre-kills-malcev-neumann-homology`, `H_i(H; D) = 0` for
`i ≤ n`. By `raag-skew-field-betti-numbers-of-finite-index-subgroups`,
`dim_D H_i(H; D) = [A_L : H] · b̃_{i−1}(L; F)`. So `b̃_j(L; F) = 0` for `j ≤ n − 1`.

Integral case: a kernel of type `FP_n(Z)` is of type `FP_n(F)` for every field `F`, so
`H̃_j(L; F) = 0` for every field and `j ≤ n − 1`. Universal coefficients give
`H̃_j(L; Z) ⊗ F ⊆ H̃_j(L; F) = 0`, and `H̃_j(L; Z)` is finitely generated, so vanishing after
`⊗ Q` and `⊗ F_p` for all primes `p` gives `H̃_j(L; Z) = 0`.
