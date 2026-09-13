---
rg: 2
id: thompson-f-has-no-faithful-2-transitive-action
kind: claim
title: Thompson's group F has no faithful 2-transitive action
distinct_from:
  thompson-f-admits-a-faithful-2-transitive-action: that claim is the affirmative answer to Problem 2.20; this claim is its negation, i.e. td(F) = 1
---

Every action of Thompson's group `F` on a set `Ω` with `|Ω| ≥ 3` fails to be
transitive on ordered pairs of distinct points. By
`thompson-f-two-transitive-actions-are-faithful`, faithfulness is automatic,
so this says the transitivity degree of `F` is 1.

## Attempts

- 2026-09-13 (z2-20-f-2-transitive), plan. Suppose `F` acts 2-transitively on
  `Ω`, and write `F_ω` for point stabilizers. For an open interval `U ⊂ (0,1)`,
  let `F_U^c` be the elements with compact support in `U`.
  - **Case I:** some `F_U^c` fixes a point. Let `O_ω` be the union of the
    intervals `U` with `F_U^c ≤ F_ω`, and `C_ω = (0,1) \ O_ω`. The map
    `ω ↦ C_ω` is equivariant. Primitivity forces it to be injective, and then
    `F_ω` is the setwise stabilizer of `C_ω`. Invariant antisymmetric
    relations (compare `inf C_ω`, `sup C_ω`, leftmost disagreement points)
    must be empty, which forces strong constraints. Analysis in progress.
  - **Case II:** no `F_U^c` fixes a point. Test confinedness of `F_ω` with the
    commutator lemma of Le Boudec–Matte Bon (arXiv:2012.03997, Theorem 3.5,
    from arXiv:2006.08677 Theorem 3.17).
  Neither case is closed.
