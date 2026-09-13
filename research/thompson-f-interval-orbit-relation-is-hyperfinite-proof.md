---
rg: 2
id: thompson-f-interval-orbit-relation-is-hyperfinite-proof
kind: route
title: The F-orbit relation on the interval is the dyadic affine relation, hence hyperfinite
target: thompson-f-interval-orbit-relation-is-hyperfinite
requires: []
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md
---

Full proof: `research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md`, §2,
Theorem B.

1. **`R_F ⊆ R_Aff`.** On each piece an element of `F` is `t ↦ 2^k t + d`, with `d` dyadic
   because breakpoints and their images are dyadic.
2. **`R_Aff ∩ (0,1)^2 ⊆ R_F`.** For `w = 2^k t + d` with `t` not dyadic:
   - take a small standard dyadic interval `I ∋ t` whose image `J = 2^k I + d` is again a
     standard dyadic interval inside `(0,1)`;
   - complete `I` and `J` to standard dyadic subdivisions of `[0,1]` with equally many pieces
     in the same positions, refining by halving to match counts;
   - by Cannon–Floyd–Parry (Enseign. Math. 42 (1996), Lemma 4.2) some `f ∈ F` maps the pieces
     affinely onto each other, so `f(t) = w`.

   Dyadic `t` is the case of transitivity of `F` on dyadic rationals.
3. **Hyperfiniteness.** Given `μ`, set `ν = sum_j 2^(-j) (g_j)_* μ` over an enumeration of
   `Aff`. It is `Aff`-quasi-invariant, and by step 2 its restriction to `(0,1)` is equivalent
   to `μ`. The orbit relation of the amenable countable group `Aff` is `ν`-amenable (Zimmer
   1977), hence `ν`-hyperfinite (Connes–Feldman–Weiss 1981). Intersecting the finite
   approximating relations with `(0,1)^2` shows `(R_F, μ)` is hyperfinite.
