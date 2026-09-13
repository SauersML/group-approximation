---
rg: 2
id: g-times-z-type-f-iff-finitely-dominated-classifying-space
kind: claim
title: "G x Z is of type F exactly when K(G,1) is finitely dominated, and then G is of type F exactly when Wall's obstruction vanishes"
distinct_from:
  g-times-z-type-f-implies-g-type-f: that is the open assertion that every such G is of type F; this is the established dictionary identifying the class of such G and the single obstruction that separates them from type F groups.
---

Let `G` be a group. The following are equivalent:

1. `G × Z` is of type F;
2. some, equivalently every, `K(G,1)` is finitely dominated;
3. `G` is finitely presented and of type FP;
4. `G` is of type `F_∞` and `cd G < ∞`.

When they hold, `G` is torsion-free. Moreover `G` is of type F exactly when
Wall's finiteness obstruction of `K(G,1)`,

```text
σ(G) = Σ_i (−1)^i [P_i]  in  K̃_0(ZG),
```

is zero, where `P_* → Z` is any finite resolution of the trivial module by
finitely generated projective `ZG`-modules. The class does not depend on the
choice of resolution.

Consequently Zaremsky's Problem 1.21 has a positive answer exactly when
`σ(G) = 0` for every finitely presented group `G` of type FP. Equivalently,
every finitely dominated aspherical CW complex is homotopy equivalent to a
finite CW complex.

The equivalence of 1 and 4 is the equivalence recorded in the problem
statement itself. The mechanism is due to Wall (the finiteness obstruction)
and Mather (the product with a circle). This node packages it with a
complete proof in [[g-times-z-type-f-iff-finitely-dominated-classifying-space-proof]].
