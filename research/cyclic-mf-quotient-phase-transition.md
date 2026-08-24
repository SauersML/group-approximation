---
rg: 2
id: cyclic-mf-quotient-phase-transition
kind: claim
title: One word classifies MF across the entire quotient lattice of one finitely presented group
distinct_from:
  literal-mark-quotient-mf: That theorem decides one specified quotient after killing its marked word; this word decides every normal quotient of one ambient group.
  profinite-twins-opposite-mf: That construction obtains profinite twins through a lamp telescope; here the identical completions come from universal factorization through the cyclic quotient.
artifacts:
  - research/cyclic-mf-quotient-phase-transition-proof.md
---

There is a finitely presented group `W`, a nontrivial element `d in W`, and
a split epimorphism `pi:W->Z` such that, for every normal subgroup `N normal
W`,

```text
cl_MF^W(N)=N normalClosure(d),

W/N is MF  iff  d belongs to N.                    (P1)
```

Moreover every homomorphism from `W` to an MF group factors uniquely through
`pi`.  The same is true for homomorphisms to finite-dimensional linear groups
over every field, finite groups, residually finite groups, compact groups,
profinite groups, and maximally almost periodic groups.

Consequently `W` and `Z` have canonically identical norm-corona
representation functors, Bohr compactifications, profinite completions, and
all-fields finite-dimensional representation functors.  Nevertheless `W`
is non-MF, while imposing the single relation `d=1` produces the MF group
`Z`.
