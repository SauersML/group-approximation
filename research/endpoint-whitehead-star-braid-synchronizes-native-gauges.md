---
rg: 2
id: endpoint-whitehead-star-braid-synchronizes-native-gauges
kind: claim
title: The endpoint Whitehead star braid synchronizes all three native gauges but does not create the first support
artifacts:
  - research/endpoint-whitehead-star-braid-proof.md
distinct_from:
  native-j1-extension-gives-gl5-but-only-second-whitehead-gram: that constructs the literal GL5 block and proves a one-third lower bound for the actual J2 compression; this extracts the new odd J1--W and J2--W occurrence relations and then computes the full algebraic obstruction to obtaining the missing J1 support from a signed-source return.
  adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges: that synchronizes the two adjacent prefix gauges after they have already been placed on one common Pauli carrier; this adds the endpoint Whitehead as a third literal actor and shows that a paired J1/u1 central sign cannot remain independent of the endpoint occurrence.
  endpoint-odd-actor-retains-native-factor-gauge: that leaves a paired gauge in the factorization M=J2(B3A2) when only the W,M actor is retained; this kills an isolated native-factor sign after J1 is adjoined, while recording that a simultaneous common endpoint sign is still allowed.
  b2-pairs-full-hecke-first-support: that adjoins the literal B2 root and proves that the first r sign has exactly half the actual full Hecke source Q; this claim's zero-support profile is deliberately only the coarser p2 actor packet without that full-source normalizer.
---

**ESTABLISHED ODD OCCURRENCE AND SUPPORT FENCE.**  Use the five literal
projective summands

```text
u_0=q@5, u_1=e_1@7, u_2=e_2@8, u_3=e_3@9, u_4=e_3@2
```

of `native-j1-extension-gives-gl5-but-only-second-whitehead-gram`.  On
their direct sum the three actual Whitehead words are

```text
J_1=(u_1 u_2),          J_2=(u_2 u_3),
W=(u_2 u_4).                                             (EWS1)
```

They are the identity off that direct sum.  Hence ordinary elementary
matrix multiplication gives the three pairwise Coxeter rows

```text
J_1WJ_1=WJ_1W,          J_2WJ_2=WJ_2W,
J_1J_2J_1=J_2J_1J_2,                                  (EWS2)
```

or equivalently

```text
(J_1W)^3=(J_2W)^3=(J_1J_2)^3=1.                       (EWS3)
```

These are relations between the literal native coefficient occurrences,
not a finite-model specialization.

Suppose a common reducing homogeneous Pauli block types their fixed label
actions as

```text
J_i=S_i tensor V_i,             W=S_W tensor V_W.      (EWS4)
```

The label swaps satisfy the same rows `(EWS2)`.  Therefore the reservoir
involutions do too.  In particular

```text
V_1 ~ V_W ~ V_2                                            (EWS5)
```

by explicit unitary conjugacy, and all three have the same positive
spectral fraction.  This is an actual Property-`(T)`-free shared-gauge
mechanism.

It also removes the isolated paired central sign in the first native Hecke
head.  Put `u_1=B_2A_1`, so `(J_1u_1)^7=1`.  If a central multiplicity
involution `D` is inserted simultaneously as

```text
J_1 |-> J_1D,                 u_1 |-> u_1D,             (EWS6)
```

then the order-seven product does not see it.  But with the endpoint
occurrence `W` fixed, `(EWS3)` gives

```text
((J_1D)W)^3=D.                                       (EWS7)
```

Thus the exact relation forces `D=1`.  If `W` is changed by the same `D`,
the change survives only as one **common endpoint gauge**, which is exactly
the shared parameter rather than an independent first-row ambiguity.

The odd row does not, by itself, create the first native support.  Recall

```text
K_2=<C_1,C_2,C_3,v,w,s>,       p_2=e_(K_2,lambda_2),
r=x_58(a_2),                   q_1=p_2 1_(r=+1).       (EWS8)
```

Let `g` be any element of the literal `GL_5(F_2)` actor which normalizes
the signed pair `(K_2,lambda_2)`.  The projective-incidence calculation
forces

```text
g r g^(-1)=r v^epsilon,             epsilon in {0,1}. (EWS9)
```

Since `v=+1` on `p_2`, every such return preserves the `r` sign.  Thus no
signed-source return in this actor exchanges `q_1` with its complement.
The exact local stabilizer profile

```text
p_2!=0,                 rp_2=-p_2                    (EWS10)
```

is consequently compatible with all returned signed-source covariance
rows and has `q_1=0`.  This is a scoped profile of the return interface,
not a representation of the whole moving Leavitt packet.

In fact the moving `J_1,W` interface itself has a finite exact support
model with this behavior.  Put

```text
r'=WrW=x_52(a_3),
A=<v,r,r',w,s,s'> ~= C_2^6.                           (EWS11)
```

The two actors generate `S_3` and simultaneously permute the triples
`(v,r,r')` and `(w,s,s')`: `J_1` swaps their first two coordinates and `W`
swaps their last two.  Take the orbit of the character

```text
(v,r,r')=(+,-,-),              (w,s,s')=(+,+,+).     (EWS12)
```

and the induced monomial representation of `A semidirect S_3`, adjoining
the fixed prescribed signs of `C_1,C_2,C_3`.  The `p_2` projection is the
single atom displayed in `(EWS12)`.  The endpoint word `W` fixes that atom,
because it exchanges the two negative entries, whereas `J_1` moves it.
Consequently this exact finite packet has

```text
p_2Wp_2=Wp_2,               q_1=p_2(J_1p_2J_1)p_2=0. (EWS13)
```

Thus even maximal endpoint Gram plus the odd `J_1--W` braid does not force
positive first support.  This is a representation of the displayed
six-root semidirect packet, not of the full `GL_5` moving-root closure.

Therefore `(EWS2)--(EWS7)` close the **gauge-parity** part of the first
native occurrence: the first head cannot carry an independent paired
central sign once it is coupled to `W`.  Equations `(EWS9)--(EWS13)` fence
support only on the coarser `p_2` actor packet.  They do not extend to the
full Hecke source `Q`: the additional literal root `B_2` normalizes `Q` and
anticommutes there with `r`, so `b2-pairs-full-hecke-first-support` proves
that the two `r` signs each occupy exactly half of `Q`.  What remains after
that strengthening is to connect this paid first sign cut to the other
typed transport on one common native carrier; it is no longer a question
of whether the first cut itself can vanish on `Q`.

No Property `(T)`, canonical trace, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
endpoint-whitehead-star-braid-proof
