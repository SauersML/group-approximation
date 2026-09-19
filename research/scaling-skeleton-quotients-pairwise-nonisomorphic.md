---
rg: 2
id: scaling-skeleton-quotients-pairwise-nonisomorphic
kind: claim
title: The scaling telescope quotients are pairwise non-isomorphic
distinct_from:
  scaling-family-pairwise-nonisomorphic: this claim distinguishes the lamp-killed telescope quotients; the root asks to distinguish the full marked groups before taking that quotient.
  literal-telescope-split-normal-form: that claim identifies only the doubling member's split quotient; this claim treats every scale and separates the quotient isomorphism types.
artifacts:
  - research/artifacts/scaling-skeleton-amenable-radical-2026-08-30.md
  - GroupApproximation/Monsters/LiteralBaseCompleteness.lean
  - GroupApproximation/Monsters/AffineSL3Scaling.lean
  - GroupApproximation/Sofic/ScalingFamilyPresentation.lean
---

**ESTABLISHED.**  For `m>=2` let `E_m` be the scaling-family
presentation, let `c_m` be its lamp generator, and put
`N_m=<<c_m>>`.  Then

```text
E_m/N_m ~= V_m
 := Z[1/m]^3 semidirect (SL_3(Z) x Z),
```

where `(s,k)` acts on `Z[1/m]^3` by `a |-> m^k s(a)`.  The groups
`V_m` are pairwise non-isomorphic.  More precisely,

```text
Rad_am(V_m) ~= Z[1/m]^3 semidirect_m Z
```

and

```text
|Tor(Rad_am(V_m)^ab)|=(m-1)^3.
```

Thus the abstract isomorphism type of the lamp-killed telescope quotient
recovers `m`.

DERIVATION
[[scaling-skeleton-amenable-radical-proof]]
