---
rg: 2
id: stw99-problem-lxiv-cu-of-villadsen-toms
kind: claim
title: Compute the Cuntz semigroup of the stable-rank-one Villadsen-Toms counterexamples (STW Problem LXIV, Gardella-Perera)
root: true
artifacts:
  - research/artifacts/stw99-structural-cu-cluster-2026-08-30.md
---

**Problem LXIV of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Gardella--Perera Questions 16.1--16.3).  What is `Cu` of the
Villadsen/Toms classification counterexamples with stable rank one —
and are there two DISTINCT `Cu`-morphisms `Cu(Z) → Cu(A)` there?

## Attempts

* Since these algebras have sr1, all ranks occur (Thiel), so
  `Cu(A) = V(A) ⊔ (soft part)` with the soft part known
  (`LAff`-type); the entire computation is the MONOID `V(A)` of
  projection classes and its interaction with softs — i.e. exactly
  the coordinate-Euler bookkeeping this session's XXVII lane
  mechanized: `V(A)` is the direct limit of Hopf-summand monoids
  under duplication maps, and the mod-`ell` Chern thresholds
  (`stw27-coordinate-euler-slack-obstructs-compact-dividers`) already
  compute which divisibility relations FAIL in `V(A)`.  The recorded
  concrete plan: present `V(A)` by generators (coordinate classes per
  stage) and the duplication relations, with the Chern criterion
  deciding order — this is a complete combinatorial description
  modulo realizing all rank-respecting inequalities, which sr1
  supplies (Thiel again).
* A `Cu`-morphism `Cu(Z) → Cu(A)` sends the compact `[1]` to a
  compact class and each soft `t` to softs of rank `t·r`; two
  DISTINCT morphisms would need either two base compacts (easy:
  different projections — presumably Gardella--Perera normalize at
  `[1]`, making the question whether the SOFT wing maps in two ways),
  and softness in sr1 algebras is governed by rank functions alone,
  so distinctness must come from `V(A)`-perforation shadowing the
  soft part.  The peer lane's soft-divider rounding theorem is the
  exact tool: below rank `n(n+1)` soft dividers are compact, so any
  second morphism differs only beyond that window — pinned as the
  place to look.  STAKES RAISED (route
  `stw99-lxiv-pair-lifts-to-lxiii-refuter`): by Robert's
  classification on the stable-rank-one target, a positive
  two-morphism answer LIFTS to two non-approximately-unitarily-
  equivalent unital embeddings `Z → A`, refuting STW Problem LXIII
  outright; so this second question is now a designated kill shot for
  the embedding-uniqueness problem.
