---
rg: 2
id: sl3-arithmetic-double-embeds-in-centralizer-hnn
kind: claim
title: The SL3 arithmetic double is the two-adjacent-vertex subgroup of the centralizer HNN group
distinct_from:
  sl3-hnn-sits-in-shulman-symmetric-double: that embeds the HNN group into a larger double built from A times Z and records an operator-norm MF firewall; this embeds the smaller double A amalgamated over C with A into the HNN group and uses only Bass--Serre normal form.
---

For any subgroup `C<=A`, let

```text
G=<A,t | [t,c]=1 (c in C)> = A *_C (C x Z).
```

Then the map

```text
A *_C A -> G,
i_0(a) |-> a,       i_1(a) |-> t a t^(-1),                    (ADE1)
```

is injective.  In particular, for
`C=SL_3(Z)<=A=SL_3(Z[1/2])`, the arithmetic double is a finitely presented
subgroup of the centralizer HNN candidate.

Indeed, Britton normal form gives

```text
A intersect t A t^(-1) = C.                                  (ADE2)
```

A reduced word alternating between `A-C` and
`t(A-C)t^(-1)` remains Britton-reduced in `G`, so it is nontrivial.  This
is exactly the normal-form criterion for injectivity of `(ADE1)`.

