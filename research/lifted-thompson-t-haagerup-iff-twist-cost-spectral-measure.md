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

## Attempts

- 2026-09-19 (swarm-0917-w14-w14-nv-pull, calibration): an independent check of the proof
  route. No gap was found, and the status stays ESTABLISHED.
  - *Suspected gap.* If `ν = Σ w_k δ_{2^{-k}}` has finite mass, then `Φ_ν` is 2-adically
    continuous. So `Φ_ν(1 + 2^J) → Φ_ν(1)`, which is bounded, and `Φ_ν` is not proper.
  - *Why step 6(B) survives.*
    - The weights `w_k = R_k^{-1/2}` tend to `∞`, so `ν` has infinite mass and is only
      σ-finite. The 2-adic continuity needs uniform convergence, which fails here.
    - For `n = 1 + 2^J`, the index `k` of step 6(B) is `J + 2`, and `n θ_k ∈ (1/4, 1/2]`.
      So `Φ_ν(n) ≥ 2 w_{J+2} → ∞`.
    - `experiments/dyadic-twist-test-2026-09-17/phi_dyadic.py` computes both cases in exact
      dyadic arithmetic.
  - *Other steps.*
    - Step 5 checks out: `U` is open because `2c − F` is lower semicontinuous, and every
      minimizer lies in `U` because `c > 0` off `0`. It also gives `ψ(s) ≤ 4∫c² dν`.
    - Step 4 checks out: the largest `j` with `4^j ≤ ψ(z^n)`.
    - Step 6(C) checks out: `ι_k(T̄)` commutes with `r_k`, so the `e(2^{-k})`-eigenspace is
      `π_k`-invariant, with `π_k(z)` scalar on it.
  - *Constraint on witnesses (elementary).*
    - `Φ_ν ≤ 4ν(R/Z)`, so every witness `ν` in (A) has infinite mass near `0`.
    - Admissibility, together with `c(θ) ≥ |e(θ) − 1| / L`, forces `∫ |e(θ) − 1|² dν < ∞`.
    - In particular, no probability measure, and no weak limit of spectral measures of unit
      vectors, witnesses (A) by itself. The unbounded rescaling `Σ_j 2^j μ_j` of step 4 is
      essential.
