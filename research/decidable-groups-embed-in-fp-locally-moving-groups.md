---
rg: 2
id: decidable-groups-embed-in-fp-locally-moving-groups
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group with a faithful action having a locally moving simple subgroup
distinct_from:
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4 and asks only for a finitely presented, finitely discriminable overgroup; this asks for a specific kind of overgroup, which is isolated by `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`, so this implies that.
  decidable-groups-embed-in-outer-extensions-of-fp-simple-groups: that asks for a finitely presented simple normal subgroup with trivial centralizer; here the simple subgroup need not be normal or finitely presented, and the monolith it generates is in general not finitely generated.
  boone-higman-conjecture: that asks for a finitely presented simple overgroup; this asks for a finitely presented overgroup acting with a locally moving simple subgroup, and no implication from that to this is known.
  permutational-boone-higman-conjecture: that asks for a finitely presented overgroup with a type (A) action; by the hand remark below that implies this, and no converse is known.
---

**OPEN.**

## Statement

For every finitely generated group `G` with solvable word problem there is a finitely
presented group `Γ ≥ G` with a faithful action on a set `X` and a subgroup `T ≤ Γ`
satisfying (top) or (fin) of `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated`:
- (top) `X` Hausdorff, `T` simple, and every rigid stabilizer `T_U` of a nonempty open
  `U` is nonabelian; or
- (fin) `Alt_fin(X) ≤ Γ`.

The model case is `V ≤ Γ ≤ Homeo(C)` with `Γ` finitely presented.

## Position

- **Implies Question 4.** By `isolated-overgroup-via-locally-moving-hosts`, this implies
  `every-decidable-group-embeds-in-an-isolated-group`.
- **Implied by the permutational class (hand remark, not checked against Zaremsky's
  text).** Suppose `G ≤ Γ_0` with a type (A) action on `S`
  (`type-a-action-gives-boone-higman-for-subgroups`). Zaremsky's twisted Brin--Thompson
  group `SV_{Γ_0}` is a finitely presented simple group of homeomorphisms of `C^S`
  containing `G`. Its elements supported in a basic cylinder contain a copy of `V` acting
  on one coordinate, so `T = SV_{Γ_0}` satisfies (top). So
  `permutational-boone-higman-conjecture` implies this claim.
- **Upgrade to Boone--Higman.** If in the (top) case with `X = C` the full group `[[Γ]]`
  is finitely presented and its local maps are clopen transitive (true once `V ≤ Γ`), then
  the node `fp-clopen-transitive-full-cantor-groups-have-type-a-actions` (landed on
  `origin/main` in commit 4935cf816, not yet in this worktree's base) gives a type (A)
  action, and `G` satisfies Boone--Higman. So the gap between this claim and
  `boone-higman-conjecture`, on Cantor hosts, is exactly the finite presentability of the
  full closure.

## Constraints on hosts (hand, each elementary)

1. **The host is not LEF.** An infinite isolated group is never LEF.
   - A finitely presented LEF group is residually finite
     (`finitely-presented-lef-groups-are-residually-finite`).
   - If `Γ` is residually finite with finite discriminating set `F`, pick a finite
     quotient injective on `F ∪ {1}`. Its kernel is a normal subgroup missing `F`, so it
     is trivial and `Γ` is finite.
   So every host built by finite approximation dies: residually finite hosts, full groups
   of residually finite minimal actions, and the simple Kazhdan LEF hosts of this
   repository. This is consistent with `thompson-v-not-lef`.
2. **Free lampshufflers die.** `FSym(H) ⋊ H` satisfies (fin), but over an infinite `H` it
   is never finitely presented (Genevois--Tessera arXiv:2401.13520, Theorem 1.5, as
   recorded in `lampshuffler-groups-are-not-fp2-over-q`). If it were, taking `H` a
   finitely presented decidable overgroup of `G` would prove this claim.
3. **One fixed `T` is not excluded by kernel-bounded complexity.** The argument of
   `outer-extension-word-problem-is-kernel-bounded` needs the simple subgroup to be
   normal and finitely generated, so that conjugates of its generators are fixed words.
   Here `T = V` is not normal, and `ncl_Γ(V)` need not be finitely generated. So `V` as a
   universal locally moving subgroup is not ruled out by that argument. This is a hand
   remark.

## Attempts

1. **Free lampshufflers (2026-09-17, lane swarm-0917-w5-bh-heretic).** *Dead.* Take a
   finitely presented decidable `H ≥ G` (Clapham) and `Γ = FSym(H) ⋊ H`, which satisfies
   (fin). This dies at finite presentation over infinite `H` (Genevois--Tessera, recorded
   in `lampshuffler-groups-are-not-fp2-over-q`). A hand attempt on `H = Z^2` showed the
   mechanism: an induction deriving far commutations of transpositions from local
   relations stalls at radial edges of the grid.
2. **Generated hosts `⟨V, ρ(H)⟩ ≤ Homeo(C)` (same lane).** *Stalls at finite
   presentation.*
   - For a faithful action `ρ` of a finitely presented decidable `H ≥ G` on `C`, the group
     `⟨V, ρ(H)⟩` satisfies (top) and is finitely generated.
   - No mechanism was found that makes it finitely presented beyond the known ones:
     contracting self-similar actions (Nekrashevych groups) and type (A) actions (twisted
     Brin--Thompson groups). Both already land in the Boone--Higman class.
   - So the open content is a finite-presentability mechanism for locally moving groups
     that does not also give fullness of the closure.
