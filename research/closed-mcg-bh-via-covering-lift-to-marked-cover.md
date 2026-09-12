---
rg: 2
id: closed-mcg-bh-via-covering-lift-to-marked-cover
kind: route
title: Excluded extension of the one-puncture covering argument to closed surfaces
target: closed-surface-mapping-class-groups-satisfy-boone-higman
requires: []
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**Dead.** Invalidated by `closed-mcgs-have-no-covering-lift-to-marked-covers`.

The intended argument follows BFFHZ, arXiv:2503.21882v2 Section 4:
1. For a closed surface `Σ` of genus `g ≥ 3`, choose a finite cover `Σ̃`, marked
   points `P ⊂ Σ̃`, and a finite-index `L ≤ Mod(Σ)` whose elements lift to
   classes fixing `P`.
2. The lifts define a homomorphism `L → Mod(Σ̃, P)`, which a
   Birman--Hilden-type theorem would make injective.
3. `Mod(Σ̃, P)` lies in the permutational Boone--Higman class by
   `punctured-surface-mcgs-satisfy-permutational-boone-higman`. Closure under
   subgroups and finite-index overgroups
   (`boone-higman-type-a-class-closed-under-finite-extensions`) then places
   `Mod(Σ)` there, and every member of that class embeds in a finitely
   presented simple group.

Step 2 cannot exist for `g ≥ 4`, even without injectivity, so the route fails
for the class of all genera `g ≥ 3`. It is recorded with `requires: []`, the
house pattern for excluded routes. The kill comes only from the `invalidates:`
key on the obstruction claim.

In genus three the same construction is equivalent to a virtual section of the
genus-3 Birman sequence. That case is recorded in the Attempts of the target.
