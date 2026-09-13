---
rg: 2
id: relative-torsion-defect-mf-radical-step
kind: claim
title: A one-sided pair that exists only modulo an MF-invisible ideal still puts its defect ideal in the MF radical
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the absolute statement, for a one-sided pair of the ring itself; this is the relative form, where the pair and the torsion of its defect hold only modulo an ideal whose relative elementary subgroup is already MF-invisible.
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

**ESTABLISHED** (route `relative-torsion-defect-mf-radical-step-proof`, artifact section 3).

Let `R` be a countable unital ring, `J` a two-sided ideal, and `n >= 4`. Suppose

```text
EL_n(R,J) <= Rad_MF(EL_n(R)),     ts - 1 in J,     m(1 - st) in J for some m >= 1.
```

Put `e = 1 - st`. Then `EL_n(R, ReR + J) <= Rad_MF(EL_n(R))`.

Two ingredients make the relative form work. First, if a normal subgroup `N` lies in
`Rad_MF(G)`, then `Rad_MF(G)` is exactly the preimage of `Rad_MF(G/N)`, so the whole question
may be pushed into `EL_n(R)/EL_n(R,J)`. Second, the proof of the absolute statement consumes only
`ts = 1`, `es = te = 0`, `f_ij f_kl = delta_jk f_il` for `f_ij = s^i e t^j`, `me = 0` and
`e != 0`; the first four are stable under reduction modulo `J`, and the fifth becomes
`e not in J`, which is the only case that needs proof.
