---
rg: 2
id: corona-defect-is-not-uniform
kind: claim
title: Corona representations of infinite groups have pointwise but not uniform defect
invalidates:
  - corona-commutant-no-growth-via-uniform-stability
distinct_from:
  countable-group-mf-conventions: That claim establishes the equivalence of the MF formulations; this one distinguishes two inequivalent notions of approximate representation and says which stability theorems can apply.
artifacts:
  - research/artifacts/glmr-2301-00476-verified.md
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

Let `Gamma` be an infinite group and `Theta : Gamma -> U(Q)` a homomorphism
into the unitary group of a norm matrix corona, with unitary lifts
`U_{gamma,n}`.  For each *fixed* pair the defect
`|| U_{gamma gamma',n} - U_{gamma,n} U_{gamma',n} ||` tends to `0`, but the
coordinate defect

```text
D_n = sup_{gamma, gamma' in Gamma} || U_{gamma gamma',n} - U_{gamma,n} U_{gamma',n} ||
```

need not tend to `0`, and there is no way to choose lifts making it do so:
the microstates are only asymptotically multiplicative on balls of slowly
growing radius.

Consequently **uniform (Ulam) stability theorems do not apply to corona
representations of infinite groups.**  Their hypothesis is smallness of `D_n`,
which is exactly what a corona representation does not supply.  This holds
whatever class of groups such a theorem covers, so the coverage question for
`Z^3 semidirect SL_3(Z)` — unresolved at source level in
`research/artifacts/glmr-2301-00476-verified.md` — does not need to be settled
before the route is closed.

The notion that does match the corona setting is **matricial stability** in
the sense of Dadarlat (Adv. Math. 2021, doi:10.1016/j.aim.2021.107722):
lifting a homomorphism into the matrix corona to a homomorphism into the
product.  That, not uniform stability, is the correct literature target for
`corona-commutant-no-growth`.
