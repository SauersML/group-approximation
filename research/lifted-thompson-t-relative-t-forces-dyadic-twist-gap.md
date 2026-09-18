---
rg: 2
id: lifted-thompson-t-relative-t-forces-dyadic-twist-gap
kind: claim
title: "If the centre of T-bar has relative (T), then Thompson's T has a uniform spectral gap for the level-k copies of a fixed generating set on vectors with no r_k-fixed part; this gap is exactly relative (T) tested on dyadic twists"
distinct_from:
  lifted-thompson-t-center-has-relative-t: that is the full relative-(T) statement; this proves it implies a strictly weaker-looking statement Gap_T, which is internal to Thompson's T, and packages both through one twist-cost function c on the circle
  lifted-thompson-t-is-a-t-menable: that node's band-cut witness form is an unwritten disintegration sketch; the dyadic part here is proved with a finite eigenspace decomposition and needs no disintegration
---

**Notation.**
- `T̄`, `z`, `t_k` and `r_k` are as in `lifted-thompson-t-quotients-are-rotation-centralizers`.
  `ι_k : T̄ → C_T(r_k) ≤ T` is the surjection there, with kernel `⟨z^{2^k}⟩` and `ι_k(z) = r_k`.
- `S` is a finite symmetric generating set of `T̄`. One exists: `T` is finitely generated
  (Cannon–Floyd–Parry), so take lifts of its generators together with `z^{±1}`.
- `L` is the `S`-word length of `z`, and `e(θ) = exp(2πiθ)`.

**Definitions.**
- *Twist cost.* For `θ ∈ R/Z`, let `c(θ)` be the infimum of `max_{s∈S} ‖π(s)ξ − ξ‖` over unitary
  representations `π` of `T̄` with `π(z) = e(θ)·I` and unit vectors `ξ`. The class is never empty:
  inducing the character `z ↦ e(θ)` from the central subgroup `⟨z⟩` gives `π(z) = e(θ)·I`.
- *Level-k gap.* For `k ≥ 1`, let `ε_k` be the infimum of `max_{s∈S} ‖ρ(ι_k(s))ξ − ξ‖` over
  unitary representations `ρ` of `T` and unit vectors `ξ ⊥ ker(ρ(r_k) − 1)`.
- `Gap_T` is the statement `inf_{k≥1} ε_k > 0`. Changing `S` changes `ε_k` by at most a factor
  given by word lengths, so the truth of `Gap_T` does not depend on `S`.

**Statement.**
- **(a) Structure of `c`.**
  - `c(0) = 0` and `c(−θ) = c(θ)`.
  - Subadditivity: `c(θ + θ') ≤ c(θ) + c(θ')`.
  - `c` is lower semicontinuous on `R/Z`.
  - Lower bound: `c(θ) ≥ |e(θ) − 1| / L`.
  - Consequently `c` vanishes only at `0`, and attains a positive minimum on every closed arc
    avoiding `0`.
- **(b) Dyadic twists are Thompson's T.**
  `inf_k ε_k ≤ inf { c(j/2^k) : k ≥ 1, 2^k ∤ j } ≤ √|S| · inf_k ε_k`.
  So `Gap_T` holds iff `liminf c(θ) > 0` as `θ → 0` through nonzero dyadic rationals.
- **(c) The target implies the gap.** If `inf_{θ ≠ 0} c(θ) = 0`, there is a cnd function on
  `T̄` that is unbounded on `⟨z⟩`. Hence `lifted-thompson-t-center-has-relative-t` implies
  `inf_{θ≠0} c > 0`, which implies `Gap_T`.

  Contrapositive, the form usable for breaking: a sequence of unitary representations `ρ_n` of
  Thompson's `T` with unit vectors `ξ_n` orthogonal to the `r_{k_n}`-fixed space and
  `max_s ‖ρ_n(ι_{k_n}(s))ξ_n − ξ_n‖ → 0` refutes `lifted-thompson-t-center-has-relative-t`. That
  kills the whole `cantor-integer-maps-central-direction-has-relative-t` refutation route of
  `brin-thompson-groups-nv-are-a-t-menable`.

**Not claimed.**
- The converse of (c), that `inf_{θ≠0} c > 0` implies relative (T) in the cnd form, is the standard
  Delorme–Guichardet direction together with a disintegration over the spectrum of `π(z)`. It is
  not written out here.
- Whether `Gap_T` implies `inf_{θ≠0} c > 0`, i.e. whether non-dyadic twists reduce to dyadic
  ones, is **open**. Subadditivity alone does not do it, because `c` is only lower semicontinuous
  and `c(θ) ≥ |e(θ) − 1|/L` rules out the "net of multiples" argument.

Derivation: route `lifted-thompson-t-relative-t-forces-dyadic-twist-gap-proof`.
