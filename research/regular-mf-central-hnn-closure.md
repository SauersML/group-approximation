---
rg: 2
id: regular-mf-central-hnn-closure
kind: claim
title: Regular operator-MF realizations are closed under central HNN extension
artifacts:
  - notes/REGULAR_MF_BASS_SERRE.md
distinct_from:
  symmetric-double-weak-mf: that proves the corresponding closure for an untwisted amalgamated double; this treats a stable letter centralizing an arbitrary subgroup.
  central-hnn-inversion-symmetrized-trace-is-mf: that is a representation-specific MF-trace lifting statement; this constructs a regular operator-MF realization and uses its trace to certify the group normal form.
---

ESTABLISHED.  Call a countable group `H` regularly operator-MF realized if
there are a separable unital MF C-star algebra `A`, an injective homomorphism
`rho:H->U(A)`, and a tracial state `tr` on `A` such that

```text
tr(rho(h))=1 if h=1, and tr(rho(h))=0 otherwise.       (RMH1)
```

For every subgroup `C<=H`, the central HNN extension

```text
G=<H,z | [z,C]=1>                                     (RMH2)
```

is regularly operator-MF realized.

Put `B=C*(rho(C))<=A`.  Shulman's central-HNN theorem makes the universal
C-star HNN algebra

```text
D=<A,z | [z,B]=0>                                     (RMH3)
```

MF.  In the GNS von Neumann algebra of `(A,tr)`, the conditional expectation
onto `rho(B)''` kills `rho(h)` for `h notin C`, by `(RMH1)`.  Mapping `(RMH3)`
to the reduced von Neumann HNN extension therefore sends every nonidentity
Britton-reduced group word to a unitary of trace zero.  This proves both that
the canonical map from `(RMH2)` into `U(D)` is injective and that the pulled
back trace is its regular character.

Every countable residually finite group has a regular realization, using a
separating chain of finite quotients with their left regular representations.
Thus `(RMH2)` is operator-MF whenever `H` is countable residually finite,
without any separability assumption on `C`.
