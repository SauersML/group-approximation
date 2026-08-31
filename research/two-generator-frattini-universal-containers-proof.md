---
rg: 2
id: two-generator-frattini-universal-containers-proof
kind: route
title: Check edge avoidance at both universal HNN stages
target: two-generator-frattini-universal-containers
requires:
  - whitehead-universal-container-via-enumeration-and-rope
  - whitehead-universal-group-via-effective-hnn-and-rope
  - whitehead-injective-two-generator-free-edge-hnn-proof
  - whitehead-injective-via-waldhausen-higman-rope
  - fournier-facio-group-is-nonsofic
  - torsion-free-finitely-presented-non-mf
  - mf-positive-controls
---

We use the following exact consequence of Collins' conjugacy theorem for an
HNN extension

```text
H=<V,t | t^(-1) A t=B>.
```

If `x,y in V`, `x` is not conjugate in `V` to an element of
`A union B`, and `x` and `y` are conjugate in `H`, then they are
already conjugate in `V`. This is the length-zero,
non-associated-subgroup case of Collins' lemma; no malnormality of `A` or
`B` is required. See Lyndon--Schupp, *Combinatorial Group Theory*,
Chapter IV, Theorem 2.5.

## 1. The universal free products

For the all-group lane, use the recursively presented free product

```text
Q=*_(i>=1) P_i
```

from [[whitehead-universal-container-via-enumeration-and-rope]]. For the
torsion-free lane, use

```text
Q_tf=*_(i>=1) T_i
```

from [[whitehead-universal-group-via-effective-hnn-and-rope]]. Every allowed
input occurs as one of the displayed free factors. Free-product normal form
shows that a factor is conjugacy-reflecting in the whole free product. The
same argument makes `Q` conjugacy-reflecting in `Q*F(a,b)`, and likewise
for `Q_tf`.

## 2. The effective two-generator compression is Frattini on the old group

Treat either free product as `Q` and put `V=Q*F(a,b)`. The compression
uses

```text
A=<b, q_i a^(-i)b a^i : i>=1>,
B=<a, b^(-i)a b^i       : i>=1>
```

and the HNN extension

```text
C=<V,t |
   t^(-1)b t=a,
   t^(-1)(q_i a^(-i)b a^i)t=b^(-i)a b^i>.
```

Let `rho:V->F(a,b)` kill `Q`. The displayed basis of `A` maps to the
free basis

```text
{b,a^(-i)b a^i:i>=1},
```

so `rho|A` is injective. The restriction to `B` is injective as well. If
a nonidentity `q in Q` were conjugate in `V` to
`z in A union B`, applying `rho` would make `rho(z)` conjugate to the
identity. Hence `rho(z)=1`, and injectivity on the relevant edge subgroup
would give `z=1`, a contradiction. Thus every nonidentity element of
`Q` avoids all `V`-conjugates of both edge subgroups. Collins' theorem
now says that conjugacy between two elements of `Q` in `C` already
occurs in `V`, and free-product normal form brings it back to `Q`.
Therefore `Q->C` is Frattini.

## 3. Higman's rope is Frattini on its input factor

Apply the existing rope to the finitely generated recursively presented
`C`. In the notation of
[[whitehead-injective-via-waldhausen-higman-rope]], its vertex group is

```text
W=P x C,
```

and its two edge maps are

```text
alpha(l)=(iota(l),1),
beta(l) =(iota(l),pi(l))
```

for `l in L`, where `iota:L->P` is injective. Let `1!=c in C`. If
`(1,c)` were conjugate in `W` to `alpha(l)` or `beta(l)`,
comparison of the first coordinates in the direct product would say that
`1` is conjugate to `iota(l)`. Thus `iota(l)=1`, hence `l=1`, so
the edge element is the identity; comparison of second coordinates would
then force `c=1`, a contradiction. Therefore `(1,c)` avoids all
conjugates of both edge subgroups. Collins' theorem says that the input copy
`(1,C)` is conjugacy-reflecting in the rope output `H`.

Only injectivity of `iota:L->P` is used here. That auxiliary embedding is
not asserted to be Frattini, and it is not an arrow on the input `C`'s
embedding path.

The existing argument makes `H` finitely presented and preserves the
exact torsion-order set. Apply the finite-presentation clause of the same
two-generator compression once more to `H`. Section 2, now with finitely
many old generators, proves that `H` is Frattini in the resulting
two-generator finitely presented group.

## 4. Compose the stages

Frattini embeddings compose: if `K->H` and `H->J` are Frattini,
conjugacy of two `K`-elements in `J` first descends to `H` and then
to `K`. Combining this observation with Sections 1--3 proves both
universal assertions.

The all-group torsion spectrum and torsion-freeness in the second lane are
exactly the torsion calculations in the two cited constructions. Each
universal free product contains the existing finitely presented nonsofic
and non-MF torsion-free witnesses. Since soficity and MF are inherited by
subgroups, neither final host has either approximation property. QED
