---
rg: 2
id: rokhlin-permanence-toolkit-sofic-closure-proof
kind: route
title: Check that each of the six Rokhlin permanence operations preserves soficity
target: rokhlin-permanence-toolkit-certifies-only-sofic-groups
requires:
  - elek-szabo-sofic-permanence
  - weakly-bernoulli-liftable-action-makes-extension-sofic
artifacts:
  - research/artifacts/gk3-rokhlin-tester-2026-09-14.md
---

Section 2 of the artifact. The sofic class contains the sofic groups, so it suffices that each operation carries sofic
groups to sofic groups. Then the sofic class is closed and contains `R`.

1. **Subgroups and finite index.** Elek–Szabó Theorem 1. For finite index, the normal core of the subgroup is sofic,
   and the quotient by it is finite, hence amenable.
2. **Local embeddings.** An injective partial multiplication map `η` on `F ∪ FF` sends good permutation models of
   `η(F ∪ FF)` to good models of `F`, since `η(1) = 1` and `η(g) != 1` for `g != 1`. A directed colimit locally embeds
   into its stages: a finite set lifts, and its finitely many coincidences occur at a later stage.
3. **Co-amenable overgroups.** Brude–Sasyk. The direct proof is Remark 4 in Section 2 of
   `research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md`, which induces permutation models along a
   Følner set of cosets with the cocycle `c(ω, g) = r(ω) g r(ωg)^-1`.
4. **Finite normal quotients.** On the points whose `N`-orbit is free and good, `τ_ḡ(O(v)) = O(σ_g v)` is well defined
   and injective. It is almost multiplicative because `N` is normal, and it is almost free because a fixed orbit forces
   `σ_(n^-1 g) v = v`. The bad set has proportion `O(δ)`.
5. **Weakly Bernoulli finite central ascent.** `weakly-bernoulli-liftable-action-makes-extension-sofic`, which needs the
   finitely presented sofic base.
