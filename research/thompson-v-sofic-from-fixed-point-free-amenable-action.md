---
rg: 2
id: thompson-v-sofic-from-fixed-point-free-amenable-action
kind: route
title: An invariant mean on a V-set without global fixed points makes the Elek–Szabó obstruction subgroup proper, hence trivial by simplicity, so V is sofic
target: thompson-v-is-sofic
requires:
  - thompson-v-has-a-fixed-point-free-amenable-action
  - elek-szabo-essentially-free-amenable-actions
  - thompson-v-finitely-presented-infinite-simple
artifacts:
  - research/artifacts/thompson-v-amenable-actions-2026-09-16.md
---

This is artifact Section 1, Theorem 1, directions (1 ⇒ 4) and "Soficity". Let `S` be a finite generating
set of `V`, and let `Ω` be a `V`-set without global fixed points that carries an invariant mean `m`. This
is `thompson-v-has-a-fixed-point-free-amenable-action`.

1. **Some generator moves a positive mass.** `Ω = ⋃_(s ∈ S) (Ω \ Fix s)`, because no point is fixed by
   all generators. So `1 ≤ Σ_(s ∈ S) m(Ω \ Fix s)`, and some `s ∈ S` has `m(Fix s) < 1`.
2. **The obstruction subgroup is proper.** In the notation of Elek–Szabó §5 (pinned in
   `elek-szabo-essentially-free-amenable-actions`), `s ∉ N_(V,Ω,m)`. Since `N_V ⊆ N_(V,Ω,m)`, we get
   `N_V ≠ V`.
3. **It is trivial.** `N_V` is a characteristic, hence normal, subgroup of the simple group `V`
   (`thompson-v-finitely-presented-infinite-simple`). So `N_V = 1`.
4. **Soficity.** Proposition 5.1(3) of Elek–Szabó says that `V/N_V = V` is sofic.

No character theory is used.

The converse fails as a route: soficity of `V` does not give item 1. The negation of the required claim
is `N_V = V`, and that is compatible with soficity.
