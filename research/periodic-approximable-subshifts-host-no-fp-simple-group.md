---
rg: 2
id: periodic-approximable-subshifts-host-no-fp-simple-group
kind: claim
title: Full groups of periodically approximable subshifts, including minimal Z-subshifts, contain no finitely presented infinite simple group
distinct_from:
  fp-subshift-full-group-subgroups-extend-to-sft: That is the extension theorem for any free subshift; this adds periodic approximations, which kill finitely presented infinite simple subgroups outright, and proves they exist for minimal Z-subshifts.
  fg-simple-hyperlinear-tree-group-not-finitely-presented: That shows Le Boudec's simple tree groups are not finitely presented, by quasi-isometry to a lamplighter; this is a symbolic-dynamics obstruction for subgroups of subshift full groups.
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

**ESTABLISHED.** Say a subshift `X ⊆ A^Lambda` has *periodic approximations*
(PA) if the following holds for every `x` in `X`, all finite `W, K ⊆ Lambda`,
and every finite `B ⊆ Lambda \ {e}`. There is a `y` in `A^Lambda` such that:
- the orbit of `y` is finite;
- `y|_W = x|_W`;
- `Stab(y) ∩ B` is empty;
- every pattern `(lambda . y)|_K` occurs in `X`.

1. If `X` is free and has (PA), then no finitely generated subgroup of
   `[[Lambda ~ X]]` is a finitely presented infinite simple group.
2. Every infinite minimal subshift of `A^Z` is free and has (PA).
3. Consequently no finitely generated subgroup of the full group of an infinite
   minimal `Z`-subshift is a finitely presented infinite simple group.
   - This includes the Juschenko--Monod groups `D([[phi]])`. That case was
     already known, by Matui's Theorem 5.7 and by the LEF theorem of
     Grigorchuk--Medynets.
   - It also includes Nekrashevych's simple periodic groups, whose fragmentation
     groups embed in such full groups (arXiv:1601.01033, source line 138; we
     read only the statement).

**Proofs.** The artifact, Section 3, gives them in full.
- **Item 1.** The SFT neighbourhood `Y` from
  `fp-subshift-full-group-subgroups-extend-to-sft` contains every
  finite-orbit `y` whose `K`-patterns occur in `X`. A generator that moves some
  `x` with cocycle `n != e` moves any such `y` agreeing with `x` on its window
  with `n` outside `Stab(y)`, contradicting the finite-orbit clause.
- **Item 2.** Given a window `[-N, N]` on which `x` is not `d`-periodic for
  `d <= max |B|`, uniform recurrence gives a later occurrence of
  `x|_{[-N, N+2M]}`. The periodic point built from the gap agrees with `x` on
  every length-`(2M+1)` window, and its least period exceeds `max |B|`.

No novelty is claimed for the `Z` case.
