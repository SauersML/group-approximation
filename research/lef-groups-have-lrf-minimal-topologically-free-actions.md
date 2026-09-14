---
rg: 2
id: lef-groups-have-lrf-minimal-topologically-free-actions
kind: claim
title: Does every finitely generated LEF group itself act minimally and topologically freely on the Cantor set with a locally residually finite action
distinct_from:
  lef-groups-embed-in-simple-kazhdan-lef-groups: that is settled, and the host is a lamplighter crossed product over an overgroup; this asks for such an action of the given group itself, which the lamplighter route does not supply.
  lrf-cantor-actions-give-lef-full-and-elementary-groups: that says what a locally residually finite minimal topologically free action gives (a combinatorial matricial model, LEF full and elementary groups); this asks which groups admit one.
  window-lef-subshifts-give-matricial-crossed-products: that is the subshift form of the hypothesis and needs a free action; this allows topological freeness and any Cantor action.
artifacts:
  - research/artifacts/sk-lef-embedding-c-review-2026-09-13.md
---

**OPEN.** Let `Γ` be finitely generated and LEF. Does `Γ` admit a minimal, topologically free action on the Cantor set
that is locally residually finite in the sense of `lrf-cantor-actions-give-lef-full-and-elementary-groups`, equivalently
whose crossed product `LC(X,F_2) ⋊ Γ` has a combinatorial matricial model?

**The converse holds.** If `Γ` has such an action then `Γ ⊆ R^×` embeds in the unit group of a ring that embeds
unitally in `∏_ω M_(N_n)(F_2)`, so `Γ` is a countable subgroup of an algebraic ultraproduct of finite groups, so `Γ`
is LEF. So the question is exactly whether the necessary condition is sufficient.

**Known cases.**
- Every finitely generated infinite residually finite `Γ`: the Toeplitz subshift of
  `rf-groups-have-free-minimal-subshifts-with-finite-models`, whose action is free with genuine finite models, and
  Kerr–Nowak residual finiteness implies LRF.
- `Γ = Z/2 ≀ Δ` for `Δ` finitely generated, infinite and LEF: the lamplighter action on `2^Δ` of
  `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`, which is minimal and topologically free, with the
  partial models `2^(Q_n) × Q_n`. This is the first family with acting groups that need not be residually finite.

**Why it is not settled by the embedding theorem.** `lef-groups-embed-in-simple-kazhdan-lef-groups` puts every
finitely generated LEF group inside a host, but the host is built from a lamplighter over an overgroup, and the given
group appears only as a subgroup of a unit group. Nothing there produces an action of the group itself.

**Test case.** The derived topological full group `[[T]]'` of a minimal subshift is finitely generated (Matui), infinite,
simple, LEF (Grigorchuk–Medynets) and therefore not residually finite. Its natural action on the Cantor set is minimal
but far from topologically free: it has elements supported on a clopen set and trivial elsewhere. I know no minimal
topologically free LRF action of it.

## Attempts

- **Restrict the lamplighter action.** For a f.g. LEF `Γ`, the action of `Γ` on `2^Γ` by shifts alone is topologically
  free but not minimal, and passing to a minimal subsystem destroys the property that every configuration is legal,
  which is what made the finite models automatic.
- **Free minimal subshifts with partial models.** Dies for free actions over non-residually-finite groups only if the
  models are genuine finite subshifts (`free-subshift-with-finite-models-forces-rf-group`). With partial models the
  window pattern sets stabilize along an ultrafilter automatically, so exactness is free, and what is missing is
  minimality and aperiodicity with bounds uniform in the model index. This is recorded in the Attempts of
  `lef-groups-embed-in-simple-kazhdan-lef-groups`.
- **Wreath trick.** `Γ ≤ Z/2 ≀ Γ`, which does have such an action, but a subgroup of a group with an LRF minimal
  topologically free action need not inherit one: the restricted action is usually not minimal.
