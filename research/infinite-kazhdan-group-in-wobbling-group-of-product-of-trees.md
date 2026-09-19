---
rg: 2
id: infinite-kazhdan-group-in-wobbling-group-of-product-of-trees
kind: claim
title: Some infinite simple Kazhdan group, and ideally every canonical input H_Γ, has a coarsely dense bounded-displacement realization on F₂×F₂
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds`, `simple-inputs-in-wobbling-hosts-are-dense-schreier-realizations`.

**OPEN.** This is the sharp test of gate U (master route, Track B) over the smallest scaffold that passes
every known necessary condition.

## Statement

Let `Λ = F₂ × F₂`. The question is whether some infinite simple group `G` with property (T) has a
nontrivial transitive action `K\G` whose Schreier graph admits an injective Lipschitz map into `Cay(Λ)`,
coarsely dense after adding finitely many or boundedly many further orbits.

The strong form asks the same for every canonical input `H_Γ`, with `Γ` decidable, and with computable
data. By `simple-inputs-in-wobbling-hosts-are-dense-schreier-realizations`, the strong form is gate U
over `F₂ × F₂` for all decidable groups, through the full group.

## What is known

- **Necessary conditions, all satisfied by `T₄ × T₄`**
  (`kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds`):
  - the Schreier graph must be one-ended and uniformly nonamenable, with exponential growth;
  - the scaffold must be nonamenable, one-ended and not virtually free.
- **Free realizations fail for monsters.** If `Γ ≤ H_Γ` contains coarsely embedded expanders, no free
  (translation-like) realization of `H_Γ` exists over `F₂ × F₂`, since `sep(T × T) ≍ n / log n`. So
  `K` must be infinite, and the Schreier graph `K\Cay(G)` must discard the expanders. Choosing a large
  stabilizer is how this is done.
- **Calibration.** Infinite simple non-Kazhdan inputs (Burger–Mozes groups) and infinite Kazhdan
  non-simple inputs over other scaffolds (Ã₂ lattices) are both realized on free orbits, by Corollary 2 of
  the dense-realization node. No Kazhdan group is known inside `W(T × T)`.

## Test cases

1. **SL₃(Z) on primitive vectors of Z³.** The Schreier graph is the "Euclid graph": edges add one
   coordinate to another. It is one-ended and uniformly nonamenable by (T). Does it embed injectively and
   Lipschitz in `T₄ × T₄`? A candidate is a map through the continued-fraction and Farey structure of
   pairs of coordinates.
2. **EL₃ of the canonical crossed-product algebra `R_Γ` on unimodular rows.** This is the natural
   parabolic action of `H_Γ` itself.

## Attempts

(none yet)
