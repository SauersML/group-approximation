---
rg: 2
id: lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure
kind: claim
title: "T-bar has the Haagerup property iff some measure nu on the circle has finite integral of the squared twist cost c and a Fourier cnd function n -> integral |e(n theta) - 1|^2 d nu that is proper; in particular square-summable dyadic twist costs give Haagerup"
distinct_from:
  lifted-thompson-t-relative-t-forces-dyadic-twist-gap: that proves one direction only (relative (T) forces inf c > 0 and the dyadic gap); this is an exact two-sided characterization of Haagerup for T-bar by the same function c, plus an explicit sufficient test on dyadic twists
  lifted-thompson-t-is-a-t-menable: that is the target property; this reduces it, with no loss, to a statement about one lower semicontinuous function on R/Z
  central-extension-haagerup-from-measurable-euler-splitting: that is a sufficient condition through a nonsingular space and a cocycle; this is necessary and sufficient and uses only unitary representations with scalar z
  lifted-thompson-t-center-has-relative-t: that is relative (T) for the centre; the characterization here shows Haagerup fails iff every admissible nu has a Fourier function with finite liminf, a subset-type condition strictly finer than relative (T) of the subgroup
---

**ESTABLISHED** by `lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure-proof`.

**Notation.**
- `T̄`, `z`, `S`, `L`, `e(θ) = exp(2πiθ)` and the twist cost `c : R/Z → [0, ∞)` are as in
  `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`.
- An *admissible measure* is a σ-finite positive Borel measure `ν` on `(R/Z) ∖ {0}` with
  `∫ c(θ)² dν(θ) < ∞`.
- Its *Fourier function* is `Φ_ν(n) = ∫ |e(nθ) − 1|² dν(θ)` for `n ∈ Z`.
  It is finite, because `|e(nθ) − 1| ≤ |n|·|e(θ) − 1| ≤ |n| L c(θ)`.

**Statement.**
- **(A) Characterization.** `T̄` has the Haagerup property iff there is an admissible `ν` with
  `Φ_ν(n) → ∞` as `|n| → ∞`.
- **(B) Dyadic test.** Suppose `0 < θ_{k+1} ≤ θ_k`, `θ_{k+1} ≥ θ_k / 2`, `θ_k → 0`, and
  `Σ_k c(θ_k)² < ∞`. Then `T̄` has the Haagerup property. In particular this holds if
  `Σ_k c(2^{-k})² < ∞`.
- **(C) Form internal to Thompson's T.** Let `ι_k : T̄ → C_T(r_k)` be as in
  `lifted-thompson-t-quotients-are-rotation-centralizers`. Suppose there are unitary
  representations `ρ_k` of `T` and unit vectors `ξ_k` with `ρ_k(r_k) ξ_k = e(2^{-k}) ξ_k` and
  `Σ_k max_{s∈S} ‖ρ_k(ι_k(s)) ξ_k − ξ_k‖² < ∞`. Then `T̄` has the Haagerup property.
  The hypothesis mentions only Thompson's `T`, its rotations `r_k` and the fixed words `ι_k(s)`.
- **(D) Where the problem now sits.** Together with
  `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`:
  - if `liminf c(θ) > 0` as `θ → 0` through dyadic rationals, then the dyadic test (B) fails;
  - if `Σ_k c(2^{-k})² < ∞`, then the target `lifted-thompson-t-is-a-t-menable` holds;
  - `T̄` fails Haagerup iff for every admissible `ν` the Fourier function has
    `liminf_{|n|→∞} Φ_ν(n) < ∞`.

**Not claimed.**
- Whether `T̄` is Haagerup. The size of `c(2^{-k})` is not computed here beyond the known bound
  `c(θ) ≥ |e(θ) − 1| / L`, which gives `c(2^{-k}) ≥ 4·2^{-k}/L` and so never blocks (B).
- That failure of Haagerup gives an infinite subset of `⟨z⟩` with relative (T) uniformly over all
  admissible `ν`. The pointwise `liminf` in (D) need not be uniform (compare the subset phenomenon
  of Chifan–Ioana, arXiv:0906.5363).

Derivation: route `lifted-thompson-t-haagerup-iff-twist-cost-spectral-measure-proof`.
