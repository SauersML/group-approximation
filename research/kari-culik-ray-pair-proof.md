---
rg: 2
id: kari-culik-ray-pair-proof
kind: route
title: Phase-zero ray - two Basic-Construction limits in KC that differ only on a vertical ray, hence no expansive direction
target: kari-culik-minimal-subsystem-has-no-expansive-direction
requires:
  - siefken-kari-culik-basic-construction-and-row-rigidity
artifacts:
  - research/artifacts/siefken-kari-culik-1410-1572-excerpts.md
  - experiments/kari-culik-diagonal-2026-09-17/seam_orbit_density.py
---

Imports, all from `siefken-kari-culik-basic-construction-and-row-rigidity`:
- (M) the multiplier property `λa + b = c + d` (bottom, left, top, right), with `λ` the row multiplier;
- (C) the multiplier of row `m` is the `λ` with `α_{m+1} = λα_m`;
- (P) Proposition 8, the Basic Construction, together with the prime rule;
- (R) Theorem 10: `Φ` is injective on `KC_{Q^c}`;
- closedness and shift invariance of `KC`.

Conventions.
- The cell `(n,m)` is column `n`, row `m`.
- `f(x) = 2x` on `[1/3,1)` and `f(x) = x/3` on `[1,2]`.
- The *angle* of a generalized Sturmian row is its symbol frequency `lim (1/L) Σ_{i<L} r_i`.
  - For `R_⌊⌋(α,t)`, every length-`L` factor has sum in `{⌊Lα⌋, ⌊Lα⌋+1}`.
  - So the angle is `α`, and it is also the angle of any limit of shifts of that row.

## Step 1. An angle-phase vector with a phase-zero half

Fix an irrational `α ∈ [1/3,2]` and put `α_m = f^m(α)` for `m ∈ Z`.
- `f` is a bijection of `[1/3,2]` that preserves irrationality, so every `α_m` is irrational and `≠ 1`.
- `f` is conjugate to an irrational rotation (Proposition 7), so `α_m < 1` for infinitely many
  negative `m`.  Let `j*` be the largest `m ≤ -1` with `α_m < 1`, and put `j_0 = j* + 1`.
  Then `α_{j_0} = 2α_{j*}`.

Define phases `t_m ∈ [0,1)`:
- `t_m = 0` for `m ≥ j_0`;
- `t_{j*} = 1/2`;
- for `m < j*`, recursively downward: `t_m = 3t_{m+1} mod 1` if `α_m ≥ 1`, and `t_m = t_{m+1}/2` if
  `α_m < 1`.

**BC property.**
- For `m ≥ j_0`, both relations read `0 = 0`.
- At `m = j*` the step is `×2`, and `t_{j_0} = 0 = 2 · (1/2) mod 1`.
- For `m < j*`:
  - if `α_m ≥ 1`, then `α_{m+1} = α_m/3` and `t_m = 3t_{m+1} mod 1` by definition;
  - if `α_m < 1`, then `α_{m+1} = 2α_m` and `t_{m+1} = 2t_m`.

**Claim 1.**  For `m ≤ j*`, `t_m = u/2^k` with `u` odd and `k ≥ 1`; in particular `t_m ∉ Z`.

*Proof.*  Induction downward from `t_{j*} = 1/2`.
- Halving `u/2^k` gives `u/2^{k+1}`.
- Tripling gives `3u/2^k mod 1`.  Its numerator stays odd because `3u` is odd, and reducing mod 1
  changes it by a multiple of `2^k`, which is even.  ∎

## Step 2. The point `y`

Let `y` be the `⌊·⌋` Basic Construction with parameters `(α_m, t_m)`.  By (P), `y ∈ KC`, and row `m` of
`Φ(y)` is `R_⌊⌋(α_m, t_m)`.

## Step 3. The point `y'`, a limit of perturbed Basic Constructions

Put `Λ_m = α_m/α > 0`, and for `ε > 0` let `t^ε_m = (t_m - εΛ_m) mod 1`, taken in `[0,1)`.

**BC property for `t^ε`.**
- If `α_{m+1} = 2α_m`, then `Λ_{m+1} = 2Λ_m`, so `t^ε_{m+1} = 2t_m - 2εΛ_m = 2t^ε_m mod 1`.
- If `α_{m+1} = α_m/3`, then `Λ_m = 3Λ_{m+1}`, so `t^ε_m = 3t_{m+1} - 3εΛ_{m+1} = 3t^ε_{m+1} mod 1`.

Let `y_ε` be the `⌊·⌋` Basic Construction for `(α_m, t^ε_m)`; by (P), `y_ε ∈ KC`.  Choose `ε_k ↓ 0`
with `y_{ε_k} → y'` (the full shift is compact).  Then `y' ∈ KC`, because `KC` is closed.

**Claim 2.**  Fix a row `m` and a column `n`.  As `ε ↓ 0`:
- if `m < j_0`, the bottom label of `y_ε` at `(n,m)` tends to that of `y`;
- if `m ≥ j_0`, it tends to `⌊nα_m⌋ - ⌊(n-1)α_m⌋` for `n ∉ {0,1}`,
  to `-1 - ⌊-α_m⌋` for `n = 0`, and to `⌊α_m⌋ + 1` for `n = 1`.

*Proof.*  Write `s = εΛ_m`, which tends to `0`.
- If `m < j_0`, then `t_m ∈ (0,1)` by Claim 1, so `t^ε_m = t_m - s` for small `ε`.  Moreover
  `iα_m + t_m ∉ Z` for every `i`, because `α_m` is irrational and `t_m` is rational and not an integer.
  So `⌊iα_m + t_m - s⌋ = ⌊iα_m + t_m⌋` for `i ∈ {n-1, n}` and small `s`.
- If `m ≥ j_0`, then `t^ε_m = 1 - s`, so the label is `⌊nα_m + 1 - s⌋ - ⌊(n-1)α_m + 1 - s⌋`.
  - For `i ≠ 0`, `iα_m ∉ Z`, so `⌊iα_m + 1 - s⌋ → ⌊iα_m⌋ + 1`.
  - For `i = 0`, `⌊1 - s⌋ = 0`.
  - Substituting `i ∈ {n-1, n}` gives the three cases.  ∎

`Φ` is continuous, being cellwise.  So `Φ(y')` is the cellwise limit in Claim 2.  With `y` from Step 2:
- `Φ(y')` and `Φ(y)` agree off `{0,1} × [j_0, ∞)`;
- in every row `m ≥ j_0`, `Φ(y')_{(0,m)} = Φ(y)_{(0,m)} - 1` and `Φ(y')_{(1,m)} = Φ(y)_{(1,m)} + 1`.

In particular `y ≠ y'`.

## Step 4. Both points lie in `KC_{Q^c}` with the same angles

Row `m` of `Φ(y)` is `R_⌊⌋(α_m, t_m)`, of angle `α_m`.  Row `m` of `Φ(y')` differs from it in at most
two entries, so it has the same frequency `α_m`.  Every `α_m` is irrational, so `y, y' ∈ KC_{Q^c}`.
By (C), `y` and `y'` have the same multiplier `λ_m` in every row `m`.

## Step 5. The two points differ, off the ray, at most by a constant left-label shift in each row

**Primes.**
- For `y` and for each `y_ε`, a bottom label `0` is primed exactly when `α_{m-1} ∈ [1/3,1/2]`, by the
  prime rule in (P).  This depends only on the common angle vector.
- Passing to the limit, the same rule holds for `y'`.
- So the full bottom labels of `y` and `y'` agree wherever `Φ(y)` and `Φ(y')` agree.
- The top label of `(n,m)` is the bottom label of `(n,m+1)`.

Hence bottom and top labels of `y` and `y'` agree at every cell outside `D = {0,1} × [j_0 - 1, ∞)`.

**Left labels.**  Let `e_m(n) = left_y(n,m) - left_{y'}(n,m)`.  The right label of `(n,m)` is the left
label of `(n+1,m)`.  Suppose `(n,m) ∉ D`.  Then (M), applied to both points with the common `λ_m` and
the common `a, c` at that cell, gives `e_m(n) = e_m(n+1)`.  So:
- for `m ≤ j_0 - 2`, `e_m(n) = δ_m` for all `n`, for a constant `δ_m`;
- for `m ≥ j_0 - 1`, `e_m(n) = δ^-_m` for all `n ≤ 0`, and `e_m(n) = δ^+_m` for all `n ≥ 2`.

## Step 6. The constants vanish

Take any of the constants: `δ = δ_m`, or `δ = δ^+_m`, or `δ = δ^-_m`.  Choose `N_k → +∞` in the
matching direction:
- columns `n = N_k` for `δ_m` or `δ^+_m`;
- columns `n = -N_k` for `δ^-_m`.

Let `σ` be the horizontal shift that moves column `±N_k` to column `0`.  Pass to a subsequence with
`σ^{±N_k} y → z` and `σ^{±N_k} y' → z'`.

**The limits.**
- `z, z' ∈ KC`, because `KC` is closed and shift-invariant.
- Row `m` of `Φ(z)` is a limit of shifts of a row of angle `α_m`.  By the factor-sum bound in the
  conventions, it has angle `α_m`.  The same holds for `z'`.  So `z, z' ∈ KC_{Q^c}`.
- `Φ(y)` and `Φ(y')` differ only in columns `0` and `1`, which run off to infinity.  So
  `Φ(z) = Φ(z')`.
- By (R), `z = z'`.

**The contradiction.**
- On one side, `left_z(0,m) = left_{z'}(0,m)`.
- On the other, `left_z(0,m) - left_{z'}(0,m) = lim e_m(±N_k) = δ`.

So `δ = 0`.

**Conclusion.**
- Every row `m ≤ j_0 - 2` has all four labels equal in `y` and `y'` at every cell.
- Every row `m ≥ j_0 - 1` has all four labels equal at every column `n ∉ {0,1}`.  At `n ≤ -1`, the
  left and right labels are `e_m(n) = e_m(n+1) = 0`, and at `n ≥ 2` they are `0` as well.
- A Wang tile is determined by its four labels.

So `y` and `y'` agree off `{0,1} × [j_0 - 1, ∞)`, and they differ by Step 3.  This proves the Theorem
of `kari-culik-minimal-subsystem-has-no-expansive-direction`.

## Corollary: no expansive direction

A line `L` through `0` is *expansive* for `KC` if, for some `w`, any two points of `KC` that agree on
the strip `L_w = {p ∈ Z^2 : dist(p, L) ≤ w}` are equal.  Fix `L` and `w`, and write `D` for the ray
set `{0,1} × [j_0 - 1, ∞)` of the Theorem.

**`L` not vertical.**
- `L_w ∩ ({0,1} × Z)` is finite; say it lies in `{0,1} × [-C, C]`.
- Let `τ` be the vertical translation moving row `j_0 - 1` to row `C + 1`.
- `τy` and `τy'` lie in `KC`, differ, and differ only on `τD ⊆ {0,1} × [C+1, ∞)`, which misses `L_w`.
- So `L` is not expansive.

**`L` vertical.**
- `L_w` is contained in the columns `|n| ≤ w`.
- Let `τ` be the horizontal translation by `⌈w⌉ + 1`.
- Then `τD` lies in columns `n > w`, and `τy ≠ τy'` agree on `L_w`.

So no line, rational or irrational, is expansive for `KC`.  Hence no primitive `v` is expansive on the
minimal subsystem `KC`, and the pair `(Σ_KC, KC)` fails the parent question at the expansiveness
requirement.  ∎

**General form.**  The same argument shows the following.  If a `Z^2` subshift `Y` has two distinct
points whose difference set lies within bounded distance of a half-line, then `Y` has no expansive
line.  This holds whatever the slope of the half-line: a non-parallel strip meets a bounded
neighbourhood of the half-line in a bounded set, and a parallel strip can be translated off it.
