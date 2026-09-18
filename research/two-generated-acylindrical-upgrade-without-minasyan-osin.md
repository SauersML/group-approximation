---
rg: 2
id: two-generated-acylindrical-upgrade-without-minasyan-osin
kind: claim
title: Every torsion-free finitely presented group normally generates a two-generated acylindrically hyperbolic overgroup, with no imported acylindricity theorem
distinct_from:
  two-generated-acylindrical-normal-generation-upgrade: same conclusion (Lemma AM2G), but that proof takes acylindrical hyperbolicity from Minasyan--Osin over a weakly malnormal edge group; this adds a second amalgam over a fixed rank-4 malnormal subgroup of F(a,b) and proves acylindricity of the tree action in-repository.
  internal-torsion-free-single-word-router: that demands a surjection from an acylindrically hyperbolic input; this gives an embedding from any torsion-free finitely presented input, which is all the consumers use.
artifacts:
  - research/two-generated-acylindrical-upgrade-without-minasyan-osin-proof.md
  - experiments/malnormal-edge-router-2026-09-17/search_malnormal.py
---

**Claim (AM2G, internal).**  Let `P` be a nontrivial finitely presented
torsion-free group.  Then there are a finitely presented, torsion-free,
two-generated group `Q_2` and an injective homomorphism `P -> Q_2` with
`normalClosure_{Q_2}(P) = Q_2`.  `Q_2` acts acylindrically and
non-elementarily on a simplicial tree, so it is acylindrically hyperbolic.

The group is

```text
Q_1 = (P * <s>) *_{C} F(a,b)          (the amalgam of two-generated-acylindrical-normal-generation-upgrade-proof, Steps 0-5; c := its b)
Q_2 = (Q_1 * <t>) *_{C'} F(a,b),
      t^4 <-> a,   s t <-> b a^2 b^2,   c t^2 <-> b a b a^{-1} b,   sc t^3 <-> b^3 a b^{-1}.
```

`C' = <a, ba^2b^2, bab a^{-1} b, b^3ab^{-1}>` is malnormal in `F(a,b)`.
`Q_2 = <t,b>`.  `Q_2/normalClosure(Q_1)` is
`G_0 = <t,b | t = b t^8 b^2, t^2 = b t^4 b t^{-4} b, t^3 = b^3 t^4 b^{-1}>`,
which is trivial.  Acylindricity comes from
`malnormal-edge-amalgam-tree-action-is-acylindrical`.

Two steps rest on finite computations in the artifact script, not on a
by-hand derivation:

* the malnormality of `C'`, by the Kapovich--Myasnikov pullback criterion on
  an 8-vertex Stallings graph, cross-checked by brute force;
* `G_0 = 1`, by Todd--Coxeter enumeration, cross-checked with SymPy's
  enumerator.

This removes the only literature import (Minasyan--Osin) from the
two-generation and acylindricity step of
`property-t-free-torsion-free-via-embedding-router`.
