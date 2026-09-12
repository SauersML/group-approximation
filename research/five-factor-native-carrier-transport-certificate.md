---
rg: 2
id: five-factor-native-carrier-transport-certificate
kind: claim
title: Five named packet-factor placements suffice for the native D8 recovery floor
distinct_from:
  forty-one-word-native-carrier-transport-certificate: that expands both carriers into 41 group-algebra support terms; this uses their native multiplicative factorizations and asks for only five packet-factor placements.
  separate-native-quarter-carrier-recovery: that asks directly for the two carrier projections to enter commuting returned algebras; this gives a stronger but finite sufficient interface in terms of the packet factors already used to define them.
---

Let `A,B` be commuting unital star-subalgebras of a finite matrix algebra.  In
the exactified Pauli packet write

```text
P_i=T_i q T_i,          F=P_0P_1,          i=0,1,
G=C^* Q C,              C=comb,            Q=Q_P.       (FFT1)
```

Here `q,Q` are projections and `T_0,T_1,C` are unitaries.  Put

```text
eta_q=dist_2(q,A),          eta_i=dist_2(T_i,A),
eta_C=dist_2(C,B),          eta_Q=dist_2(Q,B).           (FFT2)
```

Then

```text
dist_2(F,A) <= 2 eta_q+2 eta_0+2 eta_1,
dist_2(G,B) <= 2 eta_C+eta_Q.                            (FFT3)
```

Consequently the native D8 floor gives the five-factor certificate

```text
2 eta_q+2 eta_0+2 eta_1+2 eta_C+eta_Q >= 1/8.           (FFT4)
```

In particular, if all five factor-placement errors are at most `eta`, then

```text
eta >= 1/72.                                             (FFT5)
```

Thus the 41-term support audit is needed only when the decoder controls the
expanded words separately.  A decoder which chooses the two returned
algebras and is multiplicative on the native packet factors has just five
fixed placement obligations.  No permutation or character-table symmetry is
being assumed: the reduction uses the exact factorizations `(FFT1)` and hence
survives arbitrary multiplicity.

This does not by itself construct `A,B`.  Nor may the five placements be
literal universal group identities: the left regular exact packet has the
same D8 moment and would violate `(FFT4)`.  The load-bearing input remains a
finite-coordinate returned-algebra decoder; this claim makes its smallest
currently known multiplicative audit explicit.
