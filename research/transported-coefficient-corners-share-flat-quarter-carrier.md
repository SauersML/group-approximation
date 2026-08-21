---
rg: 2
id: transported-coefficient-corners-share-flat-quarter-carrier
kind: claim
title: The two transported coefficient corners share one canonical trace-quarter carrier flat against every raw character cut
artifacts:
  - experiments/atlas_transported_corner_overlap.py
  - experiments/atlas-transported-corner-overlap.json
distinct_from:
  pauli-packet-incoming-mass-exceeds-corner-capacity: that obtains a lower bound on cross-Gram overlap from capacity; this identifies an exact common projection and its complete raw-character fingerprint.
  tensor-independent-child-carrier-gap: that charges a common carrier recovered in two transverse algebras; this constructs the common transported carrier but does not yet recover it in those algebras.
---

In the exact binary Leavitt-prefix atlas packet, retain the notation

```text
q=sum_epsilon F_epsilon,       tau(q)=1/2,
T_i=comb^* B_i comb,           P_i=T_i q T_i,   i=0,1.   (TCQ1)
```

The two `P_i` are projections of trace `1/2`.  Exact rational group-algebra
reduction gives

```text
P_0P_1=P_1P_0,
F:=P_0P_1 is a projection,
tau(F)=1/4.                                             (TCQ2)
```

Equivalently, the two-projection angle operator has

```text
tau(P_0P_1)=tau((P_0P_1P_0)^2)=1/4,
tau(Z-Z^2)=0.                                          (TCQ3)
```

Thus the capacity-forced overlap actually condenses into one literal common
quarter-carrier; no soft spectral threshold or orientation choice is needed
in the exact packet.

Its raw-coordinate fingerprint is perfectly flat:

```text
tau(F F_epsilon)=3/64   for all four epsilon.           (TCQ4)
```

Consequently, for the conditional expectation onto the four-cut raw
coefficient algebra `A_0`,

```text
E_(A_0)(F)=(3/8)q,
dist_2(F,A_0)^2=23/128.                                (TCQ5)
```

In particular `F` is not a disguised raw projection (`F q != F`).  The
remaining atlas problem is now sharply phrased: use the mixed rank-five words
to recover this *already canonical and already common* projection in the two
transverse descendant algebras, or force a nontrivial holonomy while trying.

All equalities were replayed on MSI with exact rational coefficients and
exact Leavitt-prefix normal forms; no floating-point computation is involved.

