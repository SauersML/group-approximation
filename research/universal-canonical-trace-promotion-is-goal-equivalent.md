---
rg: 2
id: universal-canonical-trace-promotion-is-goal-equivalent
kind: claim
title: Existential canonical trace promotion into a group-factor corner is equivalent to a nonhyperlinear group
distinct_from:
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that gives a useful sufficient criterion from one fixed no-CE BCS algebra and an algebraic corner map; this audits the unrestricted existential von Neumann formulation and shows that it is exactly the root goal.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that proves the analogous equivalence for twisted group von Neumann algebras; this allows an arbitrary non-CE tracial algebra inside an arbitrary positive untwisted group-factor corner.
  non-ru-bcs-is-satisfiable-in-a-group-factor: that fixes the independently constructed non-RU BCS algebra and is therefore a genuine constructive transfer target; this permits choosing the source algebra after the host and is consequently tautological in the reverse direction.
artifacts:
  - research/artifacts/universal-attack-trace-promotion-audit-2026-08-22.md
---

**ESTABLISHED.**  The following are equivalent.

1. There are a countable group `G`, a nonzero projection `p in L(G)`, and a
   separable finite tracial von Neumann algebra `(M,tau)` which is not Connes
   embeddable, together with a normal trace-preserving embedding

   ```text
   M -> p L(G) p,
   ```

   where the corner carries its normalized canonical trace.
2. There is a countable nonhyperlinear group.

For `1 -> 2`, if `G` were hyperlinear then `L(G)` would be Connes embeddable;
Connes embeddability passes to nonzero corners and to tracial von Neumann
subalgebras, contradicting the choice of `M`.

For `2 -> 1`, given a countable nonhyperlinear group `G`, take

```text
M=L(G),        p=1,
```

and the identity embedding.  The canonical trace on `L(G)` is not Connes
embeddable, by the group/von-Neumann-algebra characterization of
hyperlinearity.  The optional finite-subgroup form adds nothing to this
existential statement: take the trivial finite subgroup `K={1}`, for which
`p_K=1`.

Thus a missing lemma which asks only for **at least one** non-CE tracial
algebra to embed trace-preservingly into **some** canonical group-factor
corner is not a reduction below the goal.  It is an exact reformulation of
the existence of a nonhyperlinear group.  A useful compiler must fix its
source independently (for example the explicit non-RU BCS algebra), impose
effectivity or finite presentability, or restrict the host/corner enough to
create new mathematical content.
