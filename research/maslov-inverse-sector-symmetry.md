---
rg: 2
id: maslov-inverse-sector-symmetry
kind: claim
title: An anti-symplectic outer automorphism swaps the two nontrivial mod-three Maslov sectors of Sp4(Z)
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  maslov-mod3-projective-defect-gap: that is the analytic gap to be proved; this is an exact algebraic symmetry reducing its two nontrivial multiplier cases to one.
---

Let `alpha` be the `Z/3` multiplier of the Deligne triple cover of `Sp_4(Z)`.
There is an automorphism `theta` of `Sp_4(Z)` for which

```text
theta^*[alpha] = [alpha]^{-1} = [alpha]^2.               (MIS1)
```

Equivalently, `theta` lifts to an automorphism of the triple cover `E_3` that
sends its central generator `z` to `z^{-1}`.  Hence an `alpha`-projective
almost representation of any given defect canonically yields an
`alpha^2`-projective almost representation with the same defect, and vice
versa.  It is enough to prove the projective defect gap for one nontrivial
sector.
