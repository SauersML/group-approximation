---
rg: 2
id: toms-spanning-defect-is-superadditive
kind: claim
title: The spanning defect of the level-spanning principle is superadditive under products, so the principle holds in every dimension iff the defect is sublinear, and a defect rate below 1/3 already gives linear depth for slice-constant targets
artifacts:
  - experiments/toms-relative-hex-2026-09-19/face_form_sat.py
  - experiments/toms-relative-hex-2026-09-19/results.json
distinct_from:
  toms-level-two-spanning-reduces-to-relative-hex: that proves the product rule for level components and uses it only to push a counterexample up one dimension; this turns the product rule into an amplification (a counterexample in dimension N0 gives defect k in dimension k N0), identifies the exact rate that the depth route needs, and adds an exact local SAT model of face counterexamples.
  toms-slice-constant-targets-reduce-to-level-spanning: that needs (S) exactly (defect 0) to get depth ceil(N/2); this shows that defect rate lambda < 1/3 suffices for linear depth (1 - 3 lambda) N / 2.
---

**ESTABLISHED** (internal derivation, unreviewed; proof
`toms-spanning-defect-is-superadditive-proof`). The value of `lambda` stays **OPEN**.

**Setting.** As in `toms-level-two-spanning-reduces-to-relative-hex`. For an upper
semicontinuous `delta : I^M -> Z_(>=0)` and a level component `Omega`, let `f(Omega)` be the
number of coordinates `Omega` fails face-wise (misses `x_nu = 0` or `x_nu = 1`). Define the
*spanning defect*

> `D(M) = max_delta min_Omega (f(Omega) - delta(Omega))`,

the maximum over all usc `delta` on `I^M`, the minimum over all level components. The face
form `F(M)` of the spanning principle (no face counterexample in dimension `M`) says exactly
`D(M) <= 0`.

**Theorem.**
1. *Range.* `0 <= D(M) <= M - 1`, and `D(1) = D(2) = 0`.
2. *Superadditivity.* `D(M_1 + M_2) >= D(M_1) + D(M_2)`. In particular `D` is non-decreasing.
3. *Rate.* `lambda = lim D(M)/M` exists and equals `sup_M D(M)/M`, so `D(M) <= lambda M` for
   every `M`.
4. *Amplification.* If `F(N_0)` fails, then `D(k N_0) >= k` for every `k`, and
   `D(M) >= floor(M / N_0)` for every `M`. So `F(M)` holds for every `M` iff `lambda = 0`
   iff `D(M) = o(M)`. A proof of the face form with any sublinear slack proves it exactly.
5. *Depth from the rate.* Every slice-constant target over `N` ideal two-wall windows has
   depth at least `(N - 3 D(N))/2 >= (1 - 3 lambda) N / 2`. So `lambda < 1/3` already gives
   the linear depth that `toms-overlap-window-cubes-force-linear-depth` asks for, for this
   class, and `lambda = 0` gives the known `ceil(N/2)`.

**What this changes.** The target statement for the slice-constant class is no longer the
exact principle (S) but the rate bound `lambda < 1/3`. Conversely, any single counterexample
to the face form, in any dimension `N_0`, pushes `lambda` up to at least `1/N_0` and degrades
the depth route to `(1 - 3/N_0) N / 2` at best from this argument. So a counterexample search
must look for the smallest `N_0`, and the exact SAT model below is the tool for that.

**Exact model** (`face_form_sat.py`, results in `results.json`). A face counterexample that is
constant on the open cells of the product cell complex with `n` intervals per coordinate is
the same thing as a satisfying assignment of a local formula: levels with the usc inequality
along faces, and six labels per cell ("my component misses `x_nu = 0`" / "`= 1`") that are
equal across equal-level face relations, forbidden on the corresponding face, and at least
`delta + 1` coordinates' worth. No connectivity variables are needed.
- *Calibration.* `N = 2` is UNSAT (planar Hex). Relaxing the level-2 requirement to two
  coordinates at `N = 2` is SAT at once (the slit wall of `R1(2)`).
- *`N = 3`* (the whole face form in dimension 3, which is `R1(3)` there, since levels `>= 3`
  cannot occur): UNSAT at `n = 2`; see `results.json` for larger `n`.

UNSAT at a resolution is evidence, not a proof.
