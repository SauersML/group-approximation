---
rg: 2
id: finite-unitary-canonical-trace-span-no-go
kind: claim
title: A finite unitary packet cannot both span a matrix algebra and carry canonical group trace
distinct_from:
  projective-basis-character-criterion: that characterizes projective orthonormal bases in a general tracial GNS algebra; this gives the finite-dimensional obstruction for an ordinary, rather than projective, group packet.
  controlled-central-phase-finite-group-barrier: that rules out universally sound nonlinear central selector laws in finite groups; this shows why a scalar projective center is already forced before nonlinear selector soundness is considered.
---

Let `rho:K->U(n)` be a unitary representation.  Suppose

1. `span rho(K)=M_n(C)`; and
2. normalized matrix trace agrees with the canonical group trace:

```text
tr_n(rho(g))=1  if g=e,
tr_n(rho(g))=0  if g!=e.                               (FCT1)
```

Then `n=1` and the represented group is trivial.  In particular, no
nontrivial finite matrix ancilla can simultaneously generate its whole
matrix algebra and make every nonidentity ordinary group element trace zero.

Projective Weyl/Pauli error bases do not contradict the claim: ordinary
multiplicative closure adjoins scalar phases, and those nontrivial central
scalars have nonzero normalized trace.  A protected central-character sector
is therefore structurally necessary for finite-packet groupification, not a
cosmetic feature of the toric route.

