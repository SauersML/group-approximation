---
rg: 2
id: aperiodic-sft-minimal-subsystem-with-expansive-minimal-direction
kind: claim
title: Some Z^2 SFT without periodic points has a minimal subsystem with a rational direction that is both expansive and minimal
distinct_from:
  commuting-subshift-automorphisms-die-when-space-time-is-rf: that proves the permutation-model kill of commuting-automorphism survivors fails exactly at non-RF space-time subshifts; this asks for the concrete source of such subshifts.
  minimal-z2-directions-forbid-eigenvalues-vanishing-on-them: that excludes square-hierarchical and quadratic-toral candidates; this is the existence question for the candidates it leaves.
  labbe-tiles-admit-periodic-quantum-tilings-at-every-scale: that asks whether a non-RF Z^2 shift still has matricial models; this asks for a non-RF Z^2 shift whose rows form a minimal Z-subshift carrying the vertical shift as an automorphism.
  kari-culik-minimal-subsystem-has-no-expansive-direction: that kills one candidate, the Kari--Culik SFT with Siefken's minimal subsystem, at expansiveness for every direction; this is the existence question itself.
---

**OPEN.**

**Statement.** There are:
- a `Z^2` SFT `Σ` without periodic points;
- a minimal subsystem `Y' ⊆ Σ`;
- a primitive `v ∈ Z^2` that is an expansive direction of `Y'` and acts minimally on `Y'`.

**Why it matters.**
- By `commuting-subshift-automorphisms-die-when-space-time-is-rf`, Theorem 4, a positive answer gives an
  infinite minimal subshift `X` and a `ψ ∈ Aut(X,T)` of infinite order modulo `⟨T⟩`.
- For that pair, `Y_ψ ≅ Y'` is not residually finite, so no permutation or window model of `⟨T,ψ⟩` exists.
- Then `σ_ψ` on `LC(X,F_q) ⋊ Z` is a survivor of the centralizer-compression gate
  `simple-ring-with-centralizer-compressing-automorphism` that every permutation-model kill misses.
- A negative answer does not by itself kill the survivor, because a non-residually-finite `Y_ψ` need not lie
  in an aperiodic SFT.  The obstruction there is the general window-SFT failure of
  `rf-subshifts-are-periodic-window-approximable`.

**Constraints.**
- By `minimal-z2-directions-forbid-eigenvalues-vanishing-on-them`, `Y'` has no non-cyclic finite factor.  This
  excludes Robinson and square substitutions.
- `Y'` also has no quadratic toral factor with `Γ* ∩ Q^2 = 0`.  This excludes Jeandel–Rao.

## Attempts

1. **Mozes cover of a coprime product substitution (2026-09-18, reduction, symbolic-dynamics).**
   - *Candidate.*  Let `X_1` be period doubling, with dyadic odometer factor, and `X_2` a primitive aperiodic
     length-3 substitution with a coincidence, with triadic odometer factor.
     - `X_1 × X_2` is a minimal `Z^2` subshift for `(T_1, T_2)`.
     - Every non-axis rational direction is expansive for it: a strip around `R(1,1)` contains `(m,m)` for all
       `m`, hence reads all of `x_1` and `x_2`.
     - The diagonal `(1,1)` acts minimally, since `Z_2 × Z_3` has no common eigenvalue.
     - `X_1 × X_2` itself is residually finite, as a product of residually finite `Z`-actions, so the
       candidate is its SFT cover.
   - *Cover.*  Mozes' theorem (recalled) gives a `Z^2` SFT `Σ` with a factor map `π` onto the `2 × 3` product
     substitution system.
     - `Σ` has no periodic points, because `X_1 × X_2` has none.
     - Let `Y' ⊆ Σ` be minimal, so `π(Y') = X_1 × X_2`.
   - *Remaining steps, each able to fail.*
     - (i) `π|_(Y')` is topologically almost one-to-one.  Then `(1,1)` acts minimally on `Y'`: a closed
       `(1,1)`-invariant set maps onto `X_1 × X_2`, so it contains the dense set of points with singleton
       fibres.
     - (ii) No two distinct points of `Y'` in one `π`-fibre agree on a strip around `R(1,1)`.  Then `(1,1)` is
       expansive for `Y'`, because the factor already is.
   - *Heuristic.*  Non-singleton fibres of `π` occur over configurations with an infinite vertical or
     horizontal supertile seam.  Mozes' decorations along a seam are chosen once per seam line, so the
     diagonal strip, which crosses each seam, should see them.  Neither (i) nor (ii) is checked against Mozes'
     actual tile set.

2. **Kari--Culik tiles with Siefken's minimal subsystem (2026-09-18, class kill, symbolic-dynamics).**
   - *Candidate.*
     - `Σ` is the 13-tile Kari--Culik SFT, which has no periodic points.
     - `Y' = KC` is Siefken's minimal subsystem of tilings with generalized Sturmian rows, imported in
       `siefken-kari-culik-basic-construction-and-row-rigidity`.
     - It escapes both constraints above.  Its circle eigenvalue `θ = (0, log 2/log 6)` vanishes only on
       the horizontal axis, so it passes the eigenvalue tests along every diagonal `v = (a,b)` with `ab ≠ 0`.
     - A density experiment on the invariant real-phase family finds no minimality obstruction for
       `(1,1), (1,2), (2,1), (3,1)`: `experiments/kari-culik-diagonal-2026-09-17/seam_orbit_density.py`.
   - *Kill (ESTABLISHED).*  `kari-culik-minimal-subsystem-has-no-expansive-direction` shows that `KC` has
     no expansive direction of any slope.
     - Proof: `kari-culik-ray-pair-proof`.
     - The invariant is the *phase-zero ray*.  The row multipliers `×2` and `/3` fix phase `0`, and a
       `×2` row has the two preimage phases `0` and `1/2`.
     - Setting every phase to `0` above a `×2` row and to a dyadic phase below it, then comparing the floor
       coding with a limit of left-perturbed codings, gives two points of `KC`.  They differ only on
       `{0,1} × [j_0 - 1, ∞)`.
     - Siefken's Theorem 10 (injectivity of the bottom-label map on irrational rows) forces agreement
       everywhere else.
   - *New constraint on the question.*
     - `Y'` must have no two distinct points whose difference set lies within bounded distance of a
       half-line.  Such a pair defeats every expansive direction.
     - For Attempt 1 this sharpens step (ii): a Mozes seam carrying independent decorations on two
       half-lines would be such a pair.
