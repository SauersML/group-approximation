# dgo-geometric lane report

Lane of the non-MF verbatim swarm. It owns the geometric DGO/Osin carriers and the GHW archimedean
modules `Kazhdan/GHWArchimedeanMinkowski` and `Kazhdan/GHWArchimedeanWalls`.

## 2026-09-13: GHW char 0 handed to ghw-assembly; archimedean half on main

This lane's section of ROSTER-0913 says: "Target: closed GHWCharZeroFiniteness. Also: GHWArchimedeanBound and
GHWArchimedeanSeparation green; land the in-flight files." A reassignment line in the same roster
moves GHW char 0 (`Kazhdan/GHWCharZero`, `Algebra/IntegerGridFinite`) to ghw-assembly, so this lane
has stopped its char-0 modules.

### Char 0: stopped, with one duplicate on main
- `Algebra/IntegerPolynomialUnisolvence` was landed unverified at 4896458dc and is not wired. It
  proves the same two facts as ghw-assembly's `Algebra/IntegerGridFinite` (3108f1cc7, build fix
  489b5e67a):
  - integer polynomials of bounded total degree with bounded values on an injective complex grid
    form a finite set;
  - there is an algebraically independent `ℕ → ℂ` over `ℤ`.
- Its only probe, 0913-022920-78224, is red at line 122, and the audit of
  `finite_bounded_on_grid` shows `sorryAx`.
  - Cause: in `(coeff (expVec m) G : ℂ)`, `coeff` elaborates at `ℂ`.
  - Fix: `((coeff (expVec m) G : ℤ) : ℂ)`.
- The module is off this lane's probe list. The lead decides whether it stays on main as an orphan.
- No files were written for the rest of the char-0 route. The design was: places over
  `ℤ[t_1..t_d]` for `p ∣ M` and for total degree, archimedean places over grid evaluations, then
  `GHW.hasHaagerupProperty_of_countable_places`. It matches ghw-assembly's report.

### Archimedean half
- `GHWArchimedeanBound`, `GHWArchimedeanSeparation` and `GHWArchimedeanWedge`:
  - their origin/main blobs equal 6d8971521, 448d1bf45 and 4197466c8, and all three are wired in
    the root import list;
  - sec2-sentences' probe 0912-093859-21657 built Separation;
  - probe 0912-094259-57545 was green for Bound, where `separationFinite` and
    `ghwArchimedeanAffineBound` pass `#audit_closed_axioms`;
  - a re-verification probe on the 09-13 base is running.
- `GHWArchimedeanMinkowski` and `GHWArchimedeanWalls`: origin/main equals the green landings
  b5e5abc13 and 896416980, and both are wired.

### In-flight files
- All 28 files on this lane's probe list are byte-identical to origin/main (`git hash-object`
  against the origin blob).
- 26 are imported by the root. `GGT/HypEmbeddedCentralizer` and `GGT/OsinLinealAxis` are imported
  by the wired `Manuscript/NonMF/FreeNormalSubgroupSlice` and `GGT/OsinLinealExclusion`.
- Nothing is left to land.

### Residual Props and next item
- None owned by this lane. `GHWFinitelyGeneratedCharZero` belongs to ghw-assembly.
- Next: the lead's next item.

## 2026-09-12: GHW Theorem 4, archimedean half, wall modules green

### `GroupApproximation.Kazhdan.GHWArchimedeanMinkowski`
Compiled in probes 0912-004642-27086, 0912-092049-2822 and 0912-092424-41024. Landed at b5e5abc13;
re-landed normally after 0912-092424-41024.

- Minkowski space is `Fin 4 → ℝ` through `herm`/`coords`, with `lorentzQ v = v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2`
  and polar form `lorentzB v w = v ⬝ᵥ (gram *ᵥ w)`.
- `det_gram_ne_zero : gram.det ≠ 0` (explicit `gramInv`) replaces the earlier `det_gram`.
- `conjAct g : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)` is the determinant-normalized conjugation action of
  `GL (Fin 2) ℂ`, with `conjAct_mul`, `conjAct_one`, `conjAct_inv_conjAct`, `conjAct_conjAct_inv`,
  `lorentzB_conjAct`, `abs_det_conjAct`, `measurePreserving_conjAct`,
  `conjAct_origin_of_mem_unitary` and `measurePreserving_conjAct_shell`.
- `origin = ![1, 1, 0, 0]`, `shell = {v | 1 ≤ -lorentzQ v ∧ -lorentzQ v ≤ 2}`,
  `shellMeasure = volume.restrict shell`.

### `GroupApproximation.Kazhdan.GHWArchimedeanWalls`
Green probe 0912-092424-41024 (base 896416980). Repairs were landed unverified as b9f144093, 587dde0d5
and 896416980: `open scoped symmDiff`, and a classical indicator unfolding in the norm identity. The
module was then landed normally.

- `theorem conjAct_preimage_halfSpace (g : GL (Fin 2) ℂ) (x : Fin 4 → ℝ) :
  conjAct g ⁻¹' halfSpace (conjAct g x) = halfSpace x`
- `def koopman : GL (Fin 2) ℂ →* (Lp ℝ 2 shellMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 shellMeasure)`
- `def SeparationFinite : Prop := ∀ g : GL (Fin 2) ℂ,
  shellMeasure (halfSpace (conjAct g origin) \ halfSpace origin) ≠ ⊤ ∧
  shellMeasure (halfSpace origin \ halfSpace (conjAct g origin)) ≠ ⊤`
- `theorem isCocycle_wallCocycle (hfin : SeparationFinite) :
  Delorme.IsCocycle koopman (wallCocycle hfin)`
- `theorem norm_wallCocycle_sq (hfin : SeparationFinite) (g : GL (Fin 2) ℂ) :
  ‖wallCocycle hfin g‖ ^ 2 = (shellMeasure (halfSpace origin ∆ halfSpace (conjAct g origin))).toReal`
- `def wallAction (hfin : SeparationFinite) (c : ℝ) : Haagerup.AffineAction.{0, 0} (GL (Fin 2) ℂ)`
  with `wallAction_b : (wallAction hfin c).b g = c • wallCocycle hfin g`
- `def Haagerup.AffineAction.comapHom (A : AffineAction G) (ρ : Γ →* G) : AffineAction Γ` with
  `comapHom_b`.

Every audit closure is `[propext, Classical.choice, Quot.sound]`.

### Residual (with sec2-sentences)
`SeparationFinite` is a hypothesis in Walls only. sec2-sentences discharges it in
`Kazhdan/GHWArchimedeanBound` (`separationFinite`, from `Wedge.separation_diff_lt_top`). The same
module proves `ghwArchimedeanAffineBound : GHWArchimedeanAffineBound`. When this section was
written, neither `Kazhdan/GHWArchimedeanSeparation` nor `Kazhdan/GHWArchimedeanBound` had compiled.
Both compiled later on 09-12 (see the 2026-09-13 section). Pre-probe fixes sent to sec2-sentences:

- `open scoped symmDiff` in Bound;
- drop the unused `with hg`;
- `push_neg` → `push Not` in Separation.

No census row: these modules are infrastructure for the Toeplitz–Jacobson remark (tex line 1146,
[GHW, Theorem 4]) and certify no printed sentence on their own.

### Earlier compiled landings of this lane
- `GHWInterfaces`: `GHWArchimedeanAffineBound`, `GHWComplexEmbeddingExtension`.
- `ghwComplexEmbeddingExtension` (c577ea5ec).
- `isAcylindricallyHyperbolicOsin_of_limitSet`, `isAcylindricallyHyperbolicLimitSet_iff_all` (6b5a5f75e).
- `dgoTheorem235Printed` (cebe6f695).
