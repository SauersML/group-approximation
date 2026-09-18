---
rg: 2
id: small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2
kind: claim
title: Both of Moore's radii dualize to finite linear certificates, the Ramsey one being a translate-coherent coarse one; in F_2 the window-1 Ramsey radius is 3 while every coarse Reiter radius is infinite and the window-2 Ramsey radius is already infinite; in Thompson's F the window-1 radii are R(1) = 3 and CR(1) = 5, with R(2) ≥ 9 and CR(2) ≥ 7
distinct_from:
  thompson-f-b1-ramsey-witnesses-are-at-most-one-third: that is the exact window-1 Ramsey census of F and F_2 at all precisions, which this imports; this adds the two exact duals, the coarse Reiter side, and the window-2 Ramsey side in both groups.
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that proves the sandwich R(m) ≤ CR(2m) + m and RGAP₂ ⇒ ¬AMP ⇒ RGAP₁; this re-derives its first inequality as a push-forward of dual certificates and computes both sides at m = 1, 2.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is the asymptotic ¬AMP question; this is small-radius calibration data for it and decides nothing about it.
  thompson-f-ramsey-radius-double-gap-below-reiter-radius: that is RGAP₂, asymptotic and open; this gives the first exact values of R and CR in F and shows by F_2 that R can be finite at a window where CR is infinite.
  moore-ramsey-criterion-for-amenability: that is the criterion itself; this computes its two radii at small windows.
artifacts:
  - experiments/window-two-ramsey-calibration-2026-09-17/window2.py
  - experiments/window-two-ramsey-calibration-2026-09-17/alternate.py
  - experiments/window-two-ramsey-calibration-2026-09-17/verify_witnesses.py
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_lp.py
  - experiments/window-two-ramsey-calibration-2026-09-17/free_F2_B2.json
  - experiments/window-two-ramsey-calibration-2026-09-17/thompson_F_B2_n4-8.json
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_F2_r1-5.json
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_F_r3-8.json
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_F_M2_r4-6.log
  - experiments/window-two-ramsey-calibration-2026-09-17/alternate_F_B2_n7-8.json
  - experiments/window-two-ramsey-calibration-2026-09-17/verify_alternate_F_B2_n7-8.jsonl
  - experiments/window-two-ramsey-calibration-2026-09-17/alternate_F_B2_n7-9_search.log
---

**ESTABLISHED** by `small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2-proof` (unreviewed).

**Setting.** `G` is `F = ⟨x_0, x_1⟩` or `F_2 = ⟨a, b⟩`, with `S` the two standard generators and `B_n` the word ball.
Following `moore-ramsey-criterion-for-amenability` and `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`:
- `R(m)` is the least `n` such that `B_n` is 1/2-Ramsey with respect to `B_m`.
- `CR(M)` is the least `r` such that some `ν ∈ P(B_r)` has `‖gν − ν‖₁ ≤ 1` for every `g ∈ B_M`.
- `I_n = {x : B_m x ⊆ B_n}`, and the picture of `x` under `E ⊆ B_n` is `X_E(x) = {a ∈ B_m : ax ∈ E}`.

**1. Ramsey dual.** `R(m) > n` iff there are `E ⊆ B_n` and a probability `λ` on `B_m × B_m` with
`Σ λ(a,b)(1_E(ax) − 1_E(bx)) > 1/2` for every `x ∈ I_n`. The row at `x` depends only on `X_E(x)`.

**2. Coarse Reiter dual.** `CR(M) > r` iff there is a probability `μ` on pairs `(g, D)`, with `g ∈ B_M` and
`D ⊆ B_{r+M}`, such that `Σ μ(g,D)(1_D(gx) − 1_D(x)) > 1/2` for every `x ∈ B_r`.

**3. Coherence.** The push-forward `(a, b) ↦ (b^{-1}a, b^{-1}E)` sends a Ramsey certificate at `(m, n)` to a
coarse certificate at `(2m, n − m)` with the same rows. This re-proves `R(m) ≤ CR(2m) + m`. The Ramsey
certificates are exactly the coarse certificates supported on one translate family `{(b^{-1}a, b^{-1}E)}`.

**4. F_2, coarse side.** Every finitely supported `ν` has `max_s ‖sν − ν‖₁ ≥ 1 + max ν > 1`. Hence
`CR_{F_2}(M) = ∞` for every `M ≥ 1`, and `min_{ν∈P(B_r)} max_s ‖sν − ν‖₁ = 1 + 1/|B_r|` exactly.

**5. F_2, Ramsey side.** `R_{F_2}(1) = 3`, imported. `R_{F_2}(2) = ∞`: take `E` = the reduced words beginning
with `b^{±1}`, and take `λ` uniform on
`(ba, ab^{-1}), (ba^{-1}, ab), (b², a²), (b^{-1}a, a^{-2}), (b^{-1}a^{-1}, a^{-1}b), (b^{-2}, a^{-1}b^{-1})`.
This pair has value exactly `5/6` at every radius.

**6. F, coarse side.** Let `v_M(r) = min_{ν∈P(B_r)} max_{g∈B_M} ‖gν − ν‖₁`. The following values are exact,
with matching rational primal and dual certificates:

| r | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| `v_1(r)` | 54/53 | 162/161 | 56/65 | 102/125 | 92/119 | 334/449 |

So `CR_F(1) = 5`. For `r ≤ 4`, `v_1(r)` equals the free value `1 + 1/|B_r|`. Also `v_2(4) = 3134/2387`,
`v_2(5) = 5441/4299` and `v_2(6) = 2207/1795`, so `CR_F(2) ≥ 7`.

**7. F, Ramsey side.** `R_F(1) = 3`, imported. `R_F(2) ≥ 9`. Explicit pairs `(E, λ)` with `E ⊆ B_n` have
exact minimum `3/5` at `n = 7` and `7/12` at `n = 8`. An independent script rebuilds each `E` from its
listed geodesic words and rechecks these minima.

**What this is and is not.**
- In `F_2`, set-Ramsey at window 1 is blind to what coarse Reiter sees (`R(1) = 3`, `CR(1) = ∞`), and the
  blindness costs one window doubling (`R(2) = ∞`). So `R(m) < ∞` does not bound `CR(m)`, not even in a
  group where every `CR(M)` is infinite. Any comparison of `R` and `CR` must, like the sandwich, shift the
  window.
- In `F`, `R(1) = 3 < 5 = CR(1)`. The window-1 radii of `F` and `F_2` agree on the Ramsey side and differ on
  the coarse side, and `F`'s first departure from the free values is at radius 5, the first radius where
  `|B_r(F)| < |B_r(F_2)|`.
- Not decided: any asymptotic statement, and the values of `R_F(2)` and `CR_F(2)`.
- Heuristic only, not part of the claim: alternating LP/MILP search at `n = 9` found no pair above `29/60`
  (`alternate_F_B2_n7-9_search.log`). This is a search result, not a bound.
