---
rg: 2
id: transported-coefficient-corners-share-flat-quarter-carrier
kind: claim
title: The two transported coefficient corners share one canonical trace-quarter carrier transverse to both character algebras
artifacts:
  - experiments/atlas_transported_corner_overlap.py
  - experiments/atlas-transported-corner-overlap.json
distinct_from:
  pauli-packet-incoming-mass-exceeds-corner-capacity: that obtains a lower bound on cross-Gram overlap from capacity; this identifies an exact common projection and its complete raw-character fingerprint.
  tensor-independent-child-carrier-gap: that charges a common carrier recovered in two transverse algebras; this constructs the common transported carrier but does not yet recover it in those algebras.
  pauli-carrier-membership-decoder: that asks for the branch-transfer carrier to be recovered in the raw algebra; the exact common corner here is a different projection and does not supply that decoder.
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

In particular `F` is not a disguised raw projection (`F q != F`).  The same
is true on the comb side.  If

```text
G_eta=comb^* F_eta comb,       q_comb=sum_eta G_eta,
```

then the exact table is

```text
tau(F G_eta)=1/32  for all four eta,
E_(A_comb)(F)=(1/4)q_comb,
dist_2(F,A_comb)^2=7/32,                              (TCQ6)
F q_comb != F.                                       (TCQ7)
```

Moreover `F` commutes with none of the eight raw/comb character cuts.  Thus
trace-flatness is not hidden algebra membership.

There is a second exact non-identification which matters for the atlas
ledger.  Let `Q_P` be the trace-quarter carrier in
`pauli-carrier-membership-decoder` and put

```text
Q_P^comb=comb^* Q_P comb.
```

Then

```text
F != Q_P^comb,
tau(F Q_P^comb)=1/16=tau(F)tau(Q_P^comb).             (TCQ8)
```

So the capacity-generated common corner is statistically transverse to the
previous branch-transfer carrier rather than being its missing decoder.
This falsifies the tempting direct identification of the two atlas lanes.
The remaining problem is now sharply phrased: the mixed rank-five words must
recover this *already canonical and already common* `F` in both transverse
descendant algebras, transport one of the two quarter carriers into the
other, or force nontrivial holonomy while trying.  Finite packet trace tables
alone do none of these.

All equalities were replayed on MSI with exact rational coefficients and
exact Leavitt-prefix normal forms; no floating-point computation is involved.
