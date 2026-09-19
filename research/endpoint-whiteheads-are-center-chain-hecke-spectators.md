---
rg: 2
id: endpoint-whiteheads-are-center-chain-hecke-spectators
kind: claim
title: Endpoint Whiteheads see the quarter/eighth Hecke Gram only as commuting spectators
artifacts:
  - research/endpoint-whitehead-center-chain-spectator-proof.md
distinct_from:
  endpoint-detector-cell-retains-coboundary-gauge: that transports the complete exceptional detector occurrence through the endpoint braid and leaves maximal full-source overlap; this compresses the braid by the actual nested quarter/eighth Hecke supports and obtains a nonmaximal scalar Gram, then proves why it is still occurrence-untyped.
  center-chain-hecke-polar-supports-are-nested-pauli-flags: that constructs the exact nested Hecke supports and their internal Pauli gauge; this computes the action of the fresh endpoint Whiteheads on that entire flag algebra.
  spectator-dressed-gram-does-not-share-selector-gauges: that gives an abstract finite-matrix dressing countermodel; this identifies the literal Leavitt coefficient vanishing which makes the endpoint braid precisely such a spectator dressing.
---

**ESTABLISHED MIXED-CANDIDATE FENCE.**  Use the exceptional endpoint cell
at actor coordinate `r_3=2` and choose fresh coordinates

```text
r_1=10,                  r_2=11,                  r_3=2.
```

Let `What_1,What_2` be its two adjacent prefix Whiteheads.  Retain from the
center-chain Hecke construction

```text
e=e_chi,
p_1=e z_<x_57(a_1),x_67(a_1)>,
p_2=e z_<x_57(a_1),x_67(a_1),x_68(a_2)> <= p_1,       (EHS1)
```

with

```text
tau(p_1)=(1/4)tau(e),        tau(p_2)=(1/8)tau(e).     (EHS2)
```

The endpoint Whiteheads commute with `e,p_1,p_2` and with both chained
Hecke arms `A_1=x_47(a_1),A_2=x_58(a_2)`.  Hence the compressed endpoint
transports

```text
R_1=What_1p_1,                 R_2=What_2p_2          (EHS3)
```

do have an exact nonmaximal cross Gram:

```text
G=R_1^*R_2=What_1^(-1)What_2p_2,
G^*G=p_2,
tau(G^*G)=(1/8)tau(e).                                 (EHS4)
```

Thus the first scalar requirement suggested by the endpoint-profile search
is available on the literal quarter/eighth Hecke flags.  It does **not**
break the endpoint coboundary.  Equations `(EHS3)--(EHS4)` arise solely by
compressing two commuting spectator unitaries by nested fixed projections.
The endpoint words do not conjugate either native source reflection to a
Hecke controlled target, and no mixed ordinary relation identifies their
reservoir factors with the raw gauges of the two native selector rows.

The same remains true after dressing the actual Hecke partial isometries:
for

```text
T_1=eA_1e,                    T_2=eA_2A_1e,
N_i=T_iWhat_i,                                             (EHS5)
```

the support projections remain `p_i`, while the polar factors acquire the
independent commuting endpoint gauges.  This is exactly target-word
dressing, not selector-conjugator typing.  Removing the dressing is not a
consequence of the scalar Gram or of the endpoint Coxeter braid.

There is an exact regular-trace realization of every displayed equation:
use the canonical group representation for `e,p_1,p_2,T_1,T_2` and the
literal endpoint words.  Equivalently, tensor the Hecke flag model with the
regular `S_3` endpoint reservoir.  The nested supports and `(EHS4)` remain
exact while the two endpoint gauges are nontrivial braid involutions.  Any
claim that `(EHS4)` authenticated the two affine selector rows would apply
in this fixed positive regular corner and contradict the established
regular-trace firewall.

Consequently a successful endpoint-to-Hecke attachment must be
**noncentral** at the occurrence level: it must couple an individual native
row oddly to one Hecke polar, or produce a representation-dependent proper
subrange whose discarded mass is charged by an ordinary relation defect.
The literal endpoint Whiteheads, even though they recover the correct
`1/8` scalar cross-Gram after compression, do neither.

No Property `(T)`, canonical microstate hypothesis, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
endpoint-whitehead-center-chain-spectator-proof
