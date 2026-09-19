---
rg: 2
id: anchored-pauli-extension-splits-off-its-payload
kind: claim
title: Exact Pauli covariance and two centralizing anchors split off the payload group
distinct_from:
  two-pauli-anchors-localize-arbitrary-normalizer-twists: that gives a robust matrix estimate without an actor representation; this identifies the universal group defined by the corresponding exact relations and proves it cannot create nonhyperlinearity from hyperlinear inputs.
  all-representation-expansion-keeps-macroscopic-multiplicity-swap: that obstructs localization without physical anchors; this includes the anchors, so localization succeeds but the resulting fixed-frame extension is a direct product.
---

Let `n>=3`, `V=F_2^n`, and let `P_n` be the finite Pauli group

```text
P_n={(v,phi,z): v in V, phi in V*, z in F_2},
(v,phi,z)(v',phi',z')
 =(v+v',phi+phi',z+z'+phi(v')).                           (APS1)
```

Write `x_1=(e_1,0,0)` and `z_1=(0,e_1^*,0)`.  Let a group `Q`, generated
by `a_s`, have a surjection `beta:Q->GL_n(2)`.  Its action on `P_n` is

```text
alpha_q(v,phi,z)=(beta(q)v,phi beta(q)^(-1),z).           (APS2)
```

Let `L=<t_1,...,t_k | R_L>` be any finitely generated group.  Form `G`
from the presentation of `P_n semidirect_alpha Q` and the presentation
of `L` by adding exactly the cross-relations

```text
[t_i,a_s]=[t_i,x_1]=[t_i,z_1]=1     for every i,s.        (APS3)
```

Then

```text
G ~= (P_n semidirect_alpha Q) times L.                   (APS4)
```

In particular,

```text
G is hyperlinear  iff  Q and L are hyperlinear,
G is residually finite  iff  Q and L are residually finite. (APS5)
```

This applies when `Q` is the free group on the chosen linear-actor
generators, so no actor multiplication table is imposed.  It also applies
when `Q=GL_n(2)` and that table is imposed.  With a free payload `L`, both
versions are residually finite and have exact finite-quotient canonical
microstates on every finite word window.

Thus the successful two-anchor localization step is compatible with a
hyperlinear universal group.  Any proposed nonhyperlinear construction
using it needs additional mixed relations beyond `(APS3)`, or overlapping
frames not covered by this one fixed semidirect-product presentation.
No assertion here classifies the full Toeplitz/Fanizza amalgam or a quotient
obtained by adding such mixed relations.

DERIVATION
anchored-pauli-payload-direct-product-proof
