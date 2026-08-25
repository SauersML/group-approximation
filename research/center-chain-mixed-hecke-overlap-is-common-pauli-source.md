---
rg: 2
id: center-chain-mixed-hecke-overlap-is-common-pauli-source
kind: claim
title: The mixed Hecke overlap is an exact common Pauli source with selector-factorized gauge
artifacts:
  - research/center-chain-mixed-hecke-common-source-proof.md
distinct_from:
  center-chain-mixed-hecke-polars-have-exact-overlap: that computes the scalar cross-Gram mass from the transported subgroup intersection; this proves that the overlap product is a projection, identifies both pullbacks as one source corner, and computes the relative Pauli action.
  center-chain-mixed-hecke-tail-quantitative-typing: that must still authenticate the Hecke source and target flags as the two prescribed native selector occurrences in finite canonical models; this removes the spectral, common-tail, and mixed-Pauli parts of that seam without making the forbidden fixed occurrence identification.
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that forbids promoting a fixed positive Hecke corner to both exact native selector rows; this is only an exact internal calculation on the Hecke polars and deliberately stops before native-row covariance.
---

**ESTABLISHED EXACT COMMON-SOURCE REFINEMENT.**  Retain

```text
u_1=B_2A_1,                 u_2=B_3A_2A_1,
V_i=u_iq_i,
P_i=V_iV_i^*,
```

from `center-chain-mixed-hecke-polars-share-a1-tail`, and the transported
signed subgroups

```text
L_1=H<d,v,w>,               L_2=H<f,k,vc,w,s>          (MCS1)
```

from `center-chain-mixed-hecke-polars-have-exact-overlap`.  The two range
projections commute.  More precisely, their transported characters extend
to one character `lambda` of

```text
L=<L_1,L_2>,                |L|=64*2^7,
P:=P_1P_2=e_(L,lambda).                                  (MCS2)
```

Both pullbacks of `P` are the same projection:

```text
Q:=u_1^(-1)Pu_1=u_2^(-1)Pu_2,
tau(Q)=tau(e)/128.                                         (MCS3)
```

It is the signed character projection for

```text
L_0=<H,d,f,c,k,v,w,s>,
lambda_0|_H=chi,
lambda_0(d)=lambda_0(f)=lambda_0(c)=lambda_0(k)
 =lambda_0(v)=lambda_0(w)=lambda_0(s)=+1.               (MCS4)
```

Consequently the restricted mixed polars

```text
S_i=V_iQ:QH -> PH
```

have one common source and one common range, and

```text
S_i^*S_i=Q,             S_iS_i^*=P,
G:=S_1^*S_2=(u_1^(-1)u_2)Q,
G^*G=GG^*=Q.                                              (MCS5)
```

Thus the scalar cross-Gram is not merely positive: its polar part is an
exact unitary on a fixed source corner of relative mass `1/128` inside `e`.

The corner `Q` reduces the source Pauli pair `A_1,B_1`, and

```text
[A_1,B_1]Q=x_42(q)Q=-Q.                                  (MCS6)
```

The common `A_1` tail can be separated without pretending that its first
row commutes.  Put

```text
g_1=x_87(s_(00)t_0),
U=u_1^(-1)u_2=A_1B_2B_3A_2A_1,
R=B_2UQ=g_1B_3A_2Q.                                      (MCS7)
```

Both `B_2` and `U` normalize `Q`; hence `R` is a unitary on `QH`.  Direct
Steinberg commutator collection gives

```text
[R,A_1Q]=[R,B_1Q]=0,                                    (MCS8)
UA_1U^(-1)Q=g_1A_1Q,       UB_1U^(-1)Q=B_1Q.           (MCS9)
```

Thus the only Pauli action of the relative polar before removing `B_2` is
exactly the first prescribed selector root; after removing it, the relative
gauge lies exactly in the common Pauli commutant.  No approximation,
capacity estimate, or Property `(T)` input is used.

This still does **not** identify the four Hecke flags with the actual two
native source/target selector rows.  The equal source/range corner and the
commutant gauge are internal to the Hecke construction.  Turning their
correct numerical ranks into the two prescribed native covariances remains
the finite-matrix occurrence seam, and asserting that identification on
this fixed regular corner would cross the established regular-trace
firewall.

DERIVATION
center-chain-mixed-hecke-common-source-proof

