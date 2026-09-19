---
rg: 2
id: iwahori-commensurator-nielsen-involution
kind: claim
title: The Iwahori commensurator is an explicit order-two Nielsen automorphism of Z*C2
---

Pass to the center quotient

```text
Kbar = PSL_2(Z) = <a,b | a^2=b^3=1>.
```

Let `Bbar_+` be the upper Iwahori subgroup and use the standard generators

```text
u = ab,
ell = ab^2,
e = u ell^(-2),
```

so `Bbar_+ = <u,e | e^2=1> ~= Z*C_2`.  Let

```text
sigma : Bbar_+ -> Bbar_-
```

be the Iwahori commensuration induced by conjugation with
`diag(sqrt(2),1/sqrt(2))`, and let

```text
iota = Ad(a) : Bbar_+ -> Bbar_-
```

be the ordinary inner conjugacy between the two index-three Iwahori
subgroups.  Then

```text
alpha = iota^(-1) o sigma : Bbar_+ -> Bbar_+
```

is the automorphism

```text
alpha(u) = u^(-1)e,
alpha(e) = u^(-1)e u,
```

and it is an involution:

```text
alpha^2 = id.
```

Consequently the two modular extension loci in the Dogon--Vigdorovich edge
matching problem are not unrelated subsets of the representation variety of
`Z*C_2`.  After the harmless inner conjugacy `iota`, they are one restriction
locus `E` and its image `alpha^*E` under a fixed explicit order-two Nielsen
map.  The remaining metric-regularity problem is therefore a symmetric
intersection/transversality problem for `(E,alpha^*E)`.
