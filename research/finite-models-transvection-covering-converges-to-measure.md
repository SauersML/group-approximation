---
rg: 2
id: finite-models-transvection-covering-converges-to-measure
kind: claim
title: In the finite simple models SL_3N(F_2) of G_X the number of conjugates of the model transvection over V needed for e_12(1) is N/m up to +2, and m/N accumulates only at invariant measures of V
distinct_from:
  transvection-normal-generation-recovers-invariant-measures: that counts conjugates inside the infinite group G_X; this counts them inside each finite simple model and shows the counts converge to the same value.
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part2.md
---

**Statement.** Let `X` be an infinite minimal subshift. Let `y_ℓ` be a periodic word of least period `N = N_ℓ` with the same `(2ℓ+1)`-words as `X`, and let `D_ℓ` be the model diagonal map. For a clopen `V` defined by the window `[−ℓ, ℓ]`, let `m = rank D_ℓ(χ_V) ≥ 1`. In `S = SL_{3N}(F_2)`, let `ν` be the least number of `S`-conjugates of `e_12(D_ℓ(χ_V))^{±1}` whose product is `e_12(I_N)`. Then

`N/m ≤ ν ≤ ⌊N/m⌋ + 2`, with `ν = N/m` when `m | N`.

Every limit point of `m_ℓ/N_ℓ` is `μ(V)` for a `T`-invariant `μ`. So for uniquely ergodic `X`, `ν·μ(V) → 1`.
- This matches the infinite group, where the number lies in `[1/μ(V), ⌊1/μ(V)⌋ + 3]`.
- So these normal generation numbers pass to the marked limit `G_X = lim SL_{3N_ℓ}(F_2)`, although they involve conjugators of unbounded length.

**Status: established** by `finite-models-transvection-covering-converges-to-measure-proof`. UNREVIEWED; queued with sk-verify-13.

**Review (sk-verify-15, 2026-09-13): PASS.** Rank lower bound, block conjugations in SL_{3N}(F_2), the remainder commutator, and weak* limits of periodic-orbit measures re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part2.md` §3.
