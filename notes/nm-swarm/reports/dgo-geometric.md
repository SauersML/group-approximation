# dgo-geometric lane report

Lane of the non-MF verbatim swarm. It owns the geometric DGO/Osin carriers and the GHW archimedean
modules `Kazhdan/GHWArchimedeanMinkowski` and `Kazhdan/GHWArchimedeanWalls`.

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
module proves `ghwArchimedeanAffineBound : GHWArchimedeanAffineBound`. Neither
`Kazhdan/GHWArchimedeanSeparation` nor `Kazhdan/GHWArchimedeanBound` has compiled yet. Pre-probe fixes
sent to sec2-sentences:

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
