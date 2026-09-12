---
rg: 2
id: olshanskii-g-subgroup-quotient-theorem
kind: claim
title: Olshanskii's G-subgroup theorem gives hyperbolic quotients onto which several subgroups surject
distinct_from:
  common-quotient-onto-normal-subgroup: that is Hull's small-cancellation theorem for acylindrically hyperbolic groups, whose quotients are only acylindrically hyperbolic; this is Olshanskii's theorem for word-hyperbolic groups, whose quotients stay word-hyperbolic
  relatively-hyperbolic-dehn-filling: that fills peripheral subgroups and keeps them injective; this adds relations until prescribed subgroups surject onto the whole quotient
---

Let `G` be a non-elementary word-hyperbolic group.  For a non-elementary
subgroup `X <= G` put

```text
E(X) = intersection of E(x) over the infinite-order elements x of X,
```

the unique maximal finite subgroup of `G` normalized by `X`, and let `K(X)` be
the kernel of the conjugation action of `X` on `E(G)`.

1. **Characterization.**  A non-elementary subgroup `X` is a *G-subgroup*
   (for every finite `M subset G` some epimorphism of `G` onto a
   non-elementary hyperbolic group is surjective on `X` and injective on `M`)
   iff `E(X) = E(G)` and `|X : K(X)| = |G : K(G)|`.
2. **Simultaneous surjection.**  If `H_1,...,H_k` are G-subgroups and
   `M subset G` is finite, there are a non-elementary hyperbolic group `G_1`
   and an epimorphism `φ : G -> G_1` that is injective on `M` and satisfies
   `φ(H_i) = G_1` for every `i`.  Moreover `ker φ` is torsion-free and `φ`
   induces a bijection on conjugacy classes of finite-order elements.

In particular, when `E(G) = 1`, every non-elementary subgroup `X` with
`E(X) = 1` is a G-subgroup, and any finitely many such subgroups surject
simultaneously onto one non-elementary hyperbolic quotient.

Imported; see `olshanskii-g-subgroup-quotient-citation`.
