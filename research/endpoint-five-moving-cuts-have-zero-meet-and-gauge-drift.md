---
rg: 2
id: endpoint-five-moving-cuts-have-zero-meet-and-gauge-drift
kind: claim
title: The five endpoint moving cuts have zero common meet and retain gauge coboundary drift
artifacts:
  - research/endpoint-five-moving-cut-drift-proof.md
distinct_from:
  full-packet-cyclic-aggregates-retain-positive-endpoint-gram: that proves a positive Whitehead Gram after taking the invariant orbit join; this computes the literal five individual cuts, proves their common meet is zero, and shows why the join and its positive Whitehead overlap still do not supply a fixed reservoir frame.
  moving-order-seven-stage-gauges-have-coboundary-drift: that gives the abstract seven-stage native-head fence; this proves the five-stage endpoint instance on the literal C-orbit of the signed p2 cut and combines it with the paired native-factor ambiguity.
  endpoint-odd-actor-retains-native-factor-gauge: that exhibits the paired J2/v2 factor symmetry; this shows that all five moving cuts and every actor-derived polar are invariant under that symmetry.
---

**ESTABLISHED ZERO-MEET AND MOVING-FRAME FENCE.**  Retain the literal
endpoint actor and signed source

```text
M=J_2B_3A_2,          W^2=M^7=(WM)^5=1,
C=WM,                 p=p_2,
E_j=C^j p C^(-j),     j in Z/5.                       (EMC1)
```

The five cuts have no nonzero common subprojection:

```text
meet_(j=0)^4 E_j=0.                                  (EMC2)
```

Indeed put `(e_1,e_2,e_3,e_4)=(C_3,s,t,s')` in the elementary abelian
root group of `endpoint-order-five-actor-has-half-gram`.  Since
`p_2<=1_(C_3=-1,s=+1)`, a character in the common meet would have

```text
chi(e_1)=1,                  chi(C^j e_2)=0  (0<=j<5). (EMC3)
```

The exact endpoint action gives

```text
C^j e_2 = e_2, e_3, e_1+e_4, e_1+e_2+e_3, e_4.       (EMC4)
```

The five zero equations in `(EMC3)--(EMC4)` force first
`chi(e_2)=chi(e_3)=chi(e_4)=0` and then `chi(e_1)=0`, contradicting the
first equation in `(EMC3)`.  This is an identity in the finite spectral
algebra of the literal root group, so `(EMC2)` holds in every
finite-dimensional representation, independently of its character
multiplicities.

Each individual transition is nevertheless exact and full:

```text
C E_j C^(-1)=E_(j+1).                                 (EMC5)
```

Choose packet charts on the five nonzero moving cuts and write the
reservoir factors of the compressed transitions as `D_j`.  Changing only
the reservoir frame of the `j`-th chart by a unitary `S_j` changes these
factors by the usual coboundary rule

```text
D_j |-> S_(j+1) D_j S_j^(-1),        S_5=S_0.         (EMC6)
```

Thus the relation `C^5=1` controls only the cyclic holonomy product.  It
does not identify the five factors in one fixed frame.  Concretely, after
amplifying by a two-dimensional spectator and taking a nontrivial
involution `D`, keep the initial frame fixed and choose

```text
S_0=1, S_1=D, S_2=S_3=S_4=1.                          (EMC7)
```

The same exact operators and the same five cuts are then typed with stage
factors

```text
(D_0,D_1,D_2,D_3,D_4)=(D,D,1,1,1),                  (EMC8)
```

whose product is one although `D!=1`.  This is a change of packet charts,
not a perturbation or a new representation; all transition boundaries and
all group relator defects remain exactly zero.

The positive endpoint Gram does not remove this ambiguity.  The operator
`pWp` and every projection or polar constructed inside the initial cut use
only the initial chart.  The change `(EMC7)` fixes that chart, so it leaves
the established estimate

```text
||pWp||_2^2 >= (1/3)tau(p)                            (EMC9)
```

and its polar completely unchanged while changing the first `C`-transition
factor by `D`.  Likewise, passing to the invariant join
`join_j E_j` does not create a common reducing meet: it remembers the
product occurrence `C`, whereas `(EMC2)` says there is no positive corner
on which all five stage restrictions can be compared without an additional
intertwiner.

There is a second, occurrence-level obstruction to reading a native factor
from these cuts.  The paired replacement

```text
J_2 |-> J_2 D,                 B_3A_2 |-> (B_3A_2)D  (EMC10)
```

from `endpoint-odd-actor-retains-native-factor-gauge` fixes `M`, hence fixes
`C`, every `E_j`, all `W,M,C` compressions, and every orbit join, meet, or
polar formed from them.  It changes either exposed native factor by the
nontrivial reservoir involution.  Therefore no construction functorial in
the five moving cuts and the endpoint actor can authenticate the polar as
the fixed-frame `J_2`, `B_3A_2`, or mixed-Hecke occurrence.

Consequently the global parity breaker `(WM)^5=1` cannot close the current
Hecke-carrier `C_2` grading merely by replacing a common reducing carrier
with the tautological five moving cuts.  A successful order-five compiler
must add a cross-stage fixed-frame synchronization theorem (four
independently authenticated adjacent ungauged bridges are the minimal local
spanning-tree realization), and it must also attach the endpoint `W` polar
to one literal native factor occurrence.
Positive mass, zero moving boundary, and the exact odd relator already hold;
those two occurrence statements are the missing content.

No Property `(T)`, Kazhdan input, canonical trace, computation, local
compilation, or literature theorem is used.

DERIVATION
endpoint-five-moving-cut-drift-proof
