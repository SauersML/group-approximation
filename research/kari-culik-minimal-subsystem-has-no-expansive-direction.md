---
rg: 2
id: kari-culik-minimal-subsystem-has-no-expansive-direction
kind: claim
title: The Kari--Culik minimal subsystem KC has two distinct points differing only on a vertical ray, so no direction of any slope is expansive for it
distinct_from:
  aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction: that asks for an aperiodic SFT with a minimal subsystem carrying an expansive and minimal direction; this kills the Kari--Culik SFT with KC as a candidate at the expansiveness step, for every direction.
  minimal-z2-directions-forbid-eigenvalues-vanishing-on-them: that is an eigenvalue obstruction to minimality of a direction, which KC passes along its non-axis directions; this is an obstruction to expansiveness that does not depend on eigenvalues.
  siefken-kari-culik-basic-construction-and-row-rigidity: that imports Siefken's structure theory of KC; this is a new consequence of it.
---

**ESTABLISHED** (proof: `kari-culik-ray-pair-proof`).

**Setting.**
- `Σ_KC` is the Kari--Culik SFT (13 Wang tiles, no periodic points).
- `KC ⊆ Σ_KC` is Siefken's subsystem of tilings with generalized Sturmian rows.  It is a minimal
  subsystem, by `siefken-kari-culik-basic-construction-and-row-rigidity`.

**Theorem (ray pair).**
- There are `y ≠ y'` in `KC` and `j_0 ∈ Z` with `y_(n,m) = y'_(n,m)` for every cell `(n,m)`
  (column `n`, row `m`) outside `{0,1} × [j_0 - 1, ∞)`.
- The two points share the row-angle vector `α_m = f^m(α)` for any irrational `α` one chooses.

**Corollary (no expansive direction).**  For every line `L ⊂ R^2` through `0` and every width `w`, some
translate of `(y, y')` agrees on the strip `{p ∈ Z^2 : dist(p, L) ≤ w}` but not everywhere.  So:
- `KC` has no expansive direction, rational or irrational;
- the pair `(Σ_KC, KC)` fails `aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction` for
  every `v`.

**Where it dies.**  The failure is at expansiveness, not at minimality.
- The diagonal directions `v = (a,b)` with `ab ≠ 0` pass the known minimality tests.
  - `KC` is conjugate, off a small set, to Siefken's skew product `(α,t) ↦ (α, t+α)`,
    `(α,t) ↦ f̂(α,t)`.
  - Its continuous circle eigenvalue `θ = (0, log 2/log 6)` does not vanish on such `v`.
  - An experiment finds no obstruction on the dense invariant family of real phases:
    `experiments/kari-culik-diagonal-2026-09-17/seam_orbit_density.py` gives grid coverage `1.0` for
    `(a,b) = (1,1), (1,2), (2,1), (3,1)` at levels `k = 0,1,2`.
- The invariant that kills the candidate is the *phase-zero ray*.
  - Every multiplier map `t ↦ 2t` and `t ↦ t/3` fixes the phase `0` going upward.
  - Going downward, a `×2` row has two preimage phases, `0` and `1/2`.
  - So one can keep every row phase at `0` above some row and break it below.
  - Floor and ceiling codings then differ only on the cut column of the rows above.

**Lesson for the search.**  The obstruction is structural and simple.
- A `Z^2` subshift with two distinct points agreeing outside a bounded neighbourhood of a half-line has no
  expansive direction.
- Any candidate for the parent question needs a minimal subsystem with no ray-confined difference
  pairs.
- Candidates whose rows are codings by linear multiplier maps with a common fixed phase fail this.  This
  holds for the Kari--Culik tiles with KC; other multiplier tile sets are not checked here.
