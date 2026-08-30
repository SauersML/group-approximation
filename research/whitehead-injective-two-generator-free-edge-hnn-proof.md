---
rg: 2
id: whitehead-injective-two-generator-free-edge-hnn-proof
kind: route
title: Compress through a Whitehead-acyclic free HNN edge
target: whitehead-injective-two-generator-recursive-compression
requires: [waldhausen-hnn-vertex-whitehead-injectivity, hnn-torsion-orders-equal-base-torsion-orders]
---

Choose a recursive presentation

```text
Q=<q_1,q_2,... | R>
```

and put `V=Q*F(a,b)`. Inside `V` define

```text
A=<b, q_i a^(-i)b a^i : i>=1>,
B=<a, b^(-i)a b^i       : i>=1>.
```

The displayed sets are free bases. For `B` this is the standard conjugate
basis inside `F(a,b)`. For `A`, the retraction `V->F(a,b)` killing
`Q` sends the displayed generators to the free set
`{b,a^(-i)b a^i:i>=1}`; hence no nontrivial reduced word in them can
vanish. The basis-to-basis map `A->B` is therefore an isomorphism.

Form

```text
E=<V,t |
   t^(-1)b t=a,
   t^(-1)(q_i a^(-i)b a^i)t=b^(-i)a b^i, i>=1>.
```

Normal form embeds `V`. The relations give

```text
b=t a t^(-1),
q_i=t b^(-i)a b^i t^(-1) a^(-i)b^(-1)a^i.
```

Substitution into the recursively enumerable relators `R` yields an
explicit recursively enumerable presentation of `E` on `{a,t}`.

The inclusion `Q->V` is split by the free-product retraction. The edge
`A` is a free group of countable rank, so `Wh(A)=0`: write it as the
directed union of finite-rank free factors and use `Wh(F_n)=0` together
with continuity of `K_1`. Thus
[[waldhausen-hnn-vertex-whitehead-injectivity]] makes
`Wh(V)->Wh(E)` injective, and consequently `Wh(Q)->Wh(E)` is injective.

Every finite-order element of a free product is conjugate into a factor, so

```text
Tord(V)=Tord(Q).
```

The exact HNN torsion theorem
[[hnn-torsion-orders-equal-base-torsion-orders]] then gives
`Tord(E)=Tord(V)=Tord(Q)`. QED

The index `i>=1` is essential: starting at zero would duplicate the first
basis generator.
