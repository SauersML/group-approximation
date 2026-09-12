---
rg: 2
id: a4-regular-c3-c2-character-overlap-is-flat
kind: claim
title: In the regular A4 representation the C3 and C2 character measurements are exactly unbiased
---

Let `A=<a> ~= C3` and `B=<b> ~= C2` be the standard subgroups in

```text
A4=<a,b | a^3=b^2=(ba)^3=1>.
```

Let `rho` be any multiple of the regular representation of `A4`, with normalized
trace `tau`.  For the three spectral projections `P_chi` of `rho(a)` and the two
spectral projections `Q_eps` of `rho(b)`, one has the exact flat-overlap law

```text
tau(P_chi Q_eps)=1/6
```

for every `chi in Ĉ3` and `eps in Ĉ2`.

Equivalently, conditioning the regular `A4` trace on an `a`-character leaves the
`b` sign exactly uniform, and conversely:

```text
Pr(eps | chi)=1/2,
Pr(chi | eps)=1/3.
```

Thus the **classical character-overlap channel carried by a regular A4 context
has rank one**.  Any information connecting its order-three and order-two
sides lives in noncommutative phase/coherence between the spectral blocks, not
in their scalar overlap probabilities.