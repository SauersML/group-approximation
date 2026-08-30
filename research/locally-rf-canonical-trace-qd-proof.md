---
rg: 2
id: locally-rf-canonical-trace-qd-proof
kind: route
title: Extend one finite-quotient regular representation from each finitely generated subgroup
target: locally-rf-groups-have-quasidiagonal-canonical-trace
requires: []
artifacts:
  - research/artifacts/amenable-crossed-product-trace-dichotomy-2026-08-30.md
---

Fix a finite packet in `C[K]), enlarged by the products and adjoints needed
for an operator-norm trace model, and let `H<=K` be the subgroup generated
by every group element in the packet.  It is finitely generated and hence
residually finite.  One finite quotient

```text
q:H->Q
```

separates all nonidentity elements appearing in the packet.  Compose `q`
with the left regular representation of `Q` to obtain an exact unital
star-homomorphism

```text
pi:C*_(max)(H)->M_|Q|.                                    (1)
```

Its normalized trace agrees with the canonical group trace on the chosen
packet.

The maximal subgroup inclusion
`C*_(max)(H)->C*_(max)(K)` is isometric: restriction of representations
gives one norm inequality, and induction of an arbitrary representation of
`H` to `K` gives the other.  Hence Arveson's theorem extends (1) to one
u.c.p. map

```text
phi:C*_(max)(K)->M_|Q|
```

which still equals `pi` on the whole subalgebra `C*_(max)(H)`.  On the
chosen packet the operator-norm multiplicative defect of `phi` is therefore
exactly zero, and its matrix trace is exactly the canonical trace.

Approximate an arbitrary finite packet in `C*_(max)(K)` by the group ring,
then use u.c.p. contractivity.  A diagonal exhaustion gives u.c.p. maps which
are asymptotically multiplicative in operator norm and recover the canonical
trace.  This is precisely quasidiagonality of the trace.
