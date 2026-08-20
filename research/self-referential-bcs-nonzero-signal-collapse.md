---
rg: 2
id: self-referential-bcs-nonzero-signal-collapse
kind: claim
title: A computable finite BCS has a nonzero projection erased by every asymptotically perfect finite-dimensional strategy
distinct_from:
  self-referential-perfect-zpc-irs-gap: that produces a perfect generalized IRS strategy separated from finite-dimensional quantum strategies; this produces one algebraically nonzero BCS projection with an explicit linear signal-collapse modulus.
  non-ce-bcs-has-robust-approximate-energy-gap: that starts from a tracial BCS with no Connes-embeddable trace and forces total contextual defect; this isolates one marked projection but does not assert that the resulting BCS algebra has any trace.
---

There is an effectively specified finite Boolean constraint system `B_*`, a
distinguished involution `x_D` in its BCS algebra, and a computable positive
integer `C_*` such that, for

```text
D=(1-x_D)/2,
```

one has

```text
D!=0 in A(B_*),                                                   (SBS1)

every epsilon-perfect strategy S for the BCS game satisfies
phi_S(D)<=C_* epsilon.                                           (SBS2)
```

Consequently every exact finite-dimensional star-representation of
`A(B_*)` kills `D`: its normalized trace produces a perfect synchronous
strategy, `(SBS2)` gives trace zero on the projection `D`, and positivity
then gives `pi(D)=0`.

The construction is a direct recursion-theorem diagonal against formal
vanishing of the distinguished signal. It packages the user's proposed
"program which contains its own approximation challenge" as a rigorous
finite BCS source object. It is not yet a nonhyperlinear group because the
nonlinear BCS relations are algebra relations rather than scalar group-word
relations.
