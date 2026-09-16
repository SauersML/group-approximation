---
rg: 2
id: bvc-groups-splitting-over-vc-subgroups-are-vc
kind: claim
title: A group with BVC that splits over a virtually cyclic subgroup is virtually cyclic
distinct_from:
  bvc-amalgams-have-two-transitive-vertex-actions: that gives the double coset condition |C\A/C| = 2 for an arbitrary edge group and finiteness only for finite C; this concludes that the whole group is virtually cyclic for every virtually cyclic edge group, and also covers HNN extensions
  non-ascending-hnn-extensions-lack-bvc: that excludes non-ascending HNN extensions over any subgroups; this also excludes ascending HNN extensions with an infinite virtually cyclic base, and amalgams
artifacts:
  - research/artifacts/bvc-vc-splittings-2026-09-16.md
---

**Statement.** Let `G` have property BVC. Suppose that either

- `G = A *_C B` with `C != A`, `C != B` and `C` virtually cyclic, or
- `G = <H, t | t x t^{-1} = theta(x), x in C>` for an isomorphism `theta: C -> C'` between
  subgroups of `H`, with `C` virtually cyclic.

Then `C` is finite and `G` is virtually cyclic. In the amalgam case `[A:C] = [B:C] = 2` and
`G/C ≅ D_∞`. In the HNN case `C = C' = H` is finite and `G ≅ H ⋊ Z`.

No finite generation is assumed.

**Consequences.**

- A non-virtually-cyclic group with BVC has no nontrivial one-edge splitting over a virtually
  cyclic subgroup. For example, it is not an amalgam or HNN extension over a finite subgroup,
  and it is not an ascending HNN extension of a virtually cyclic group. (It is not virtually
  free either, but that follows from von Puttkamer–Wu Lemmas 1.10 and 1.11, not from this
  claim.)
- With `fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension`: if a finitely presented,
  non-virtually-cyclic BVC group maps onto `Z`, the ascending base `H` is infinite and not
  virtually cyclic.

**How.** Three steps; the details are in the artifact.

1. Finite index. The double coset condition gives `[A:C] = 1 + [C : C ∩ aCa^{-1}]`. A finite
   intersection makes both factors finite, because length-two products `ab` fall into boundedly
   many classes, at most `|C ∩ aCa^{-1}|` per class.
2. Index two. Kill a normal infinite cyclic `Z <= C`. The quotient is an amalgam of finite groups
   that still has "every element conjugate into finitely many VC subgroups". Counting cyclically
   reduced words of length `2m` gives at least `((p-1)(q-1))^m / m` classes, against a uniform
   bound, so `p = q = 2`.
3. Conclude. `G/C ≅ D_∞`, and an infinite `C` would make `G` virtually solvable and not virtually
   cyclic. HNN extensions reduce to ascending ones over a VC base, which are virtually solvable.

**Novelty (referee, 2026-09-16).** This is not new as a theorem. Its content follows, with no
finite generation assumed, from results already in the literature and the graph, plus the same
elementary glue:

- *Some `C ∩ aCa^{-1}` finite.* `C` is weakly malnormal, so `G` is virtually cyclic or
  acylindrically hyperbolic by Minasyan–Osin (arXiv:1310.6289, Corollary 2.2; imported here as
  `fpbs-minasyan-osin-weakly-malnormal-splittings`). Acylindrically hyperbolic groups lack BVC
  (von Puttkamer–Wu 1607.03790, Proposition 3.2).
- *Otherwise.* The factors are VC by `bvc-amalgams-have-two-transitive-vertex-actions` and
  (V1), and `G/Z` is an amalgam of finite groups. It is virtually
  cyclic or acylindrically hyperbolic by the same corollary, and von Puttkamer–Wu Corollary 3.4
  (a group mapping onto an acylindrically hyperbolic group lacks BVC) excludes the second case.
  Then `G` is virtually polycyclic, and Proposition 1.12 applies.
- *HNN extensions.* von Puttkamer–Wu Lemma 2.4 and Proposition 1.12.

What the artifact adds is a self-contained proof that uses only the normal form and conjugacy
theorems for amalgams and the landed claims named in the proof route. It replaces Minasyan–Osin
by the elementary rigidity and counting Lemmas 2 and 4. The referee checked these statement
numbers against the arXiv LaTeX sources on 2026-09-16.

Proof: `bvc-groups-splitting-over-vc-subgroups-are-vc-proof`.
