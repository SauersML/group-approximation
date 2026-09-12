import GroupApproximation.Kazhdan.GHWArchimedeanMinkowski
import GroupApproximation.External.TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Walls of Minkowski space and an affine action of `GL_2(ℂ)`

Guentner--Higson--Weinberger's Lemma 8 (*The Novikov conjecture for linear groups*, Publ. Math.
IHÉS 101 (2005), §5): the displacement on `SL(2, ℂ)/SU(2)` is of negative type.  GHW give no proof
of it, only a citation.  The negative-type function here is built from walls, not hyperbolic
geometry.

A space-like vector `v` (in the shell `1 ≤ −Q(v) ≤ 2`, `Kazhdan/GHWArchimedeanMinkowski`) cuts
Minkowski space by the half-space `{x | 0 < B(x, v)}`.  For a point `x`, the walls on its positive
side form `halfSpace x = {v | 0 < B(x, v)}`.  The action `conjAct` preserves `B` and Lebesgue measure
on the shell, so it moves these sets among themselves (`conjAct_preimage_halfSpace`) and acts on
`L²(shell)` by isometries (`koopman`).  The cocycle

`b(g) = 1_{halfSpace (g · origin)} − 1_{halfSpace origin}`

satisfies `b(gh) = b(g) + π(g) b(h)` (`isCocycle_wallCocycle`), and
`‖b(g)‖² = μ(halfSpace origin ∆ halfSpace (g · origin))` (`norm_wallCocycle_sq`).  So the
displacement is of negative type with no computation.  Its growth comes from a separate
computation of the separating set (`Kazhdan/GHWArchimedeanSeparation`, lane sec2-sentences).  That
module also supplies `SeparationFinite`, which this module carries as an explicit hypothesis.

## Manuscript status

Infrastructure for the Toeplitz--Jacobson remark (tex line 1146, [GHW, Theorem 4]); certifies no
printed sentence on its own.
-/

namespace GroupApproximation
namespace GHW
namespace Walls

open Minkowski MeasureTheory
open scoped ENNReal symmDiff

noncomputable section

/-! ## Half-spaces -/

/-- **The walls on the positive side of `x`.** -/
def halfSpace (x : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := {v | 0 < lorentzB x v}

theorem measurable_lorentzB (x : Fin 4 → ℝ) : Measurable (lorentzB x) := by
  have e : lorentzB x = fun v => (x 0 * v 1 + x 1 * v 0) / 2 - x 2 * v 2 - x 3 * v 3 :=
    funext (lorentzB_apply x)
  rw [e]
  fun_prop

theorem measurableSet_halfSpace (x : Fin 4 → ℝ) : MeasurableSet (halfSpace x) :=
  measurableSet_lt measurable_const (measurable_lorentzB x)

theorem conjAct_preimage_halfSpace (g : GL (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    conjAct g ⁻¹' halfSpace (conjAct g x) = halfSpace x := by
  ext v
  simp only [halfSpace, Set.mem_preimage, Set.mem_setOf_eq, lorentzB_conjAct]

theorem conjAct_inv_preimage_halfSpace (g : GL (Fin 2) ℂ) (x : Fin 4 → ℝ) :
    conjAct g⁻¹ ⁻¹' halfSpace x = halfSpace (conjAct g x) := by
  ext v
  simp only [halfSpace, Set.mem_preimage, Set.mem_setOf_eq]
  rw [← lorentzB_conjAct g x (conjAct g⁻¹ v), conjAct_conjAct_inv]

/-! ## The Koopman representation -/

theorem conjAct_inv_comp_conjAct (g : GL (Fin 2) ℂ) :
    (conjAct g⁻¹ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) ∘ conjAct g = id :=
  funext fun v => conjAct_inv_conjAct g v

/-- The isometry `f ↦ f ∘ conjAct g⁻¹` of `L²(shell)`. -/
def koopmanEquiv (g : GL (Fin 2) ℂ) : Lp ℝ 2 shellMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 shellMeasure :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_conjAct_shell g⁻¹)
    (measurePreserving_conjAct_shell g)
    (Filter.EventuallyEq.of_eq (conjAct_inv_comp_conjAct g))

theorem coeFn_koopmanEquiv (g : GL (Fin 2) ℂ) (f : Lp ℝ 2 shellMeasure) :
    (koopmanEquiv g f : (Fin 4 → ℝ) → ℝ) =ᵐ[shellMeasure] f ∘ conjAct g⁻¹ := by
  rw [koopmanEquiv, Lp.compMeasurePreservingₗᵢEquiv_apply]
  exact Lp.coeFn_compMeasurePreserving f _

/-- **The Koopman representation of `GL_2(ℂ)` on `L²(shell)`.** -/
theorem koopmanEquiv_one : koopmanEquiv 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro f
  rw [LinearIsometryEquiv.coe_one, id]
  refine Lp.ext ((coeFn_koopmanEquiv 1 f).trans (Filter.EventuallyEq.of_eq ?_))
  funext v
  show (f : (Fin 4 → ℝ) → ℝ) (conjAct 1⁻¹ v) = (f : (Fin 4 → ℝ) → ℝ) v
  rw [inv_one, conjAct_one, LinearMap.id_apply]

theorem koopmanEquiv_mul (g h : GL (Fin 2) ℂ) :
    koopmanEquiv (g * h) = koopmanEquiv g * koopmanEquiv h := by
  apply LinearIsometryEquiv.ext
  intro f
  rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
  refine Lp.ext ((coeFn_koopmanEquiv (g * h) f).trans ?_)
  refine ((coeFn_koopmanEquiv g (koopmanEquiv h f)).trans ?_).symm
  refine ((measurePreserving_conjAct_shell g⁻¹).quasiMeasurePreserving.ae_eq_comp
    (coeFn_koopmanEquiv h f)).trans (Filter.EventuallyEq.of_eq ?_)
  funext v
  show (f : (Fin 4 → ℝ) → ℝ) (conjAct h⁻¹ (conjAct g⁻¹ v)) =
    (f : (Fin 4 → ℝ) → ℝ) (conjAct (g * h)⁻¹ v)
  rw [mul_inv_rev, conjAct_mul, LinearMap.comp_apply]

def koopman : GL (Fin 2) ℂ →* (Lp ℝ 2 shellMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 shellMeasure) where
  toFun := koopmanEquiv
  map_one' := koopmanEquiv_one
  map_mul' := koopmanEquiv_mul

theorem coeFn_koopman (g : GL (Fin 2) ℂ) (f : Lp ℝ 2 shellMeasure) :
    (koopman g f : (Fin 4 → ℝ) → ℝ) =ᵐ[shellMeasure] f ∘ conjAct g⁻¹ :=
  coeFn_koopmanEquiv g f

/-! ## The cocycle -/

/-- **Finiteness of the separating walls**, carried as a hypothesis; proved in
`Kazhdan/GHWArchimedeanSeparation`. -/
def SeparationFinite : Prop :=
  ∀ g : GL (Fin 2) ℂ,
    shellMeasure (halfSpace (conjAct g origin) \ halfSpace origin) ≠ ⊤ ∧
      shellMeasure (halfSpace origin \ halfSpace (conjAct g origin)) ≠ ⊤

/-- **The wall cocycle** `1_{halfSpace (g · origin)} − 1_{halfSpace origin}`. -/
def wallCocycle (hfin : SeparationFinite) (g : GL (Fin 2) ℂ) : Lp ℝ 2 shellMeasure :=
  indicatorConstLp 2 ((measurableSet_halfSpace _).diff (measurableSet_halfSpace _))
      (hfin g).1 (1 : ℝ) -
    indicatorConstLp 2 ((measurableSet_halfSpace _).diff (measurableSet_halfSpace _))
      (hfin g).2 (1 : ℝ)

theorem indicator_diff_sub_indicator_diff (A B : Set (Fin 4 → ℝ)) (v : Fin 4 → ℝ) :
    (A \ B).indicator (fun _ => (1 : ℝ)) v - (B \ A).indicator (fun _ => (1 : ℝ)) v =
      A.indicator (fun _ => (1 : ℝ)) v - B.indicator (fun _ => (1 : ℝ)) v := by
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;> simp [hA, hB]

theorem coeFn_wallCocycle (hfin : SeparationFinite) (g : GL (Fin 2) ℂ) :
    (wallCocycle hfin g : (Fin 4 → ℝ) → ℝ) =ᵐ[shellMeasure]
      fun v => (halfSpace (conjAct g origin)).indicator (fun _ => (1 : ℝ)) v -
        (halfSpace origin).indicator (fun _ => (1 : ℝ)) v := by
  filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 ((measurableSet_halfSpace _).diff
      (measurableSet_halfSpace _)) (hfin g).1 (1 : ℝ))
      (indicatorConstLp 2 ((measurableSet_halfSpace _).diff (measurableSet_halfSpace _))
        (hfin g).2 (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := shellMeasure)
      (hs := (measurableSet_halfSpace (conjAct g origin)).diff (measurableSet_halfSpace origin))
      (hμs := (hfin g).1) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := shellMeasure)
      (hs := (measurableSet_halfSpace origin).diff (measurableSet_halfSpace (conjAct g origin)))
      (hμs := (hfin g).2) (c := (1 : ℝ))] with v h1 h2 h3
  rw [wallCocycle, h1, Pi.sub_apply, h2, h3]
  exact indicator_diff_sub_indicator_diff _ _ v

theorem isCocycle_wallCocycle (hfin : SeparationFinite) :
    Delorme.IsCocycle koopman (wallCocycle hfin) := by
  intro g h
  refine Lp.ext ?_
  have hπ := (measurePreserving_conjAct_shell g⁻¹).quasiMeasurePreserving.ae_eq_comp
    (coeFn_wallCocycle hfin h)
  filter_upwards [coeFn_wallCocycle hfin (g * h),
    Lp.coeFn_add (wallCocycle hfin g) (koopman g (wallCocycle hfin h)),
    coeFn_wallCocycle hfin g, coeFn_koopman g (wallCocycle hfin h), hπ] with v h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5]
  simp only [Function.comp_apply]
  have e1 : conjAct g⁻¹ v ∈ halfSpace (conjAct h origin) ↔
      v ∈ halfSpace (conjAct (g * h) origin) := by
    rw [← Set.mem_preimage, conjAct_inv_preimage_halfSpace, conjAct_mul, LinearMap.comp_apply]
  have e2 : conjAct g⁻¹ v ∈ halfSpace origin ↔ v ∈ halfSpace (conjAct g origin) := by
    rw [← Set.mem_preimage, conjAct_inv_preimage_halfSpace]
  by_cases a1 : v ∈ halfSpace (conjAct (g * h) origin) <;>
    by_cases a2 : v ∈ halfSpace (conjAct g origin) <;>
      by_cases a3 : v ∈ halfSpace origin <;>
        simp [a1, a2, a3, e1, e2]

/-- **‖b(g)‖² is the measure of the separating walls.** -/
theorem norm_wallCocycle_sq (hfin : SeparationFinite) (g : GL (Fin 2) ℂ) :
    ‖wallCocycle hfin g‖ ^ 2 =
      (shellMeasure (halfSpace origin ∆ halfSpace (conjAct g origin))).toReal := by
  have hsep : MeasurableSet (halfSpace origin ∆ halfSpace (conjAct g origin)) :=
    (measurableSet_halfSpace _).symmDiff (measurableSet_halfSpace _)
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have hae : (fun v => inner ℝ ((wallCocycle hfin g : (Fin 4 → ℝ) → ℝ) v)
      ((wallCocycle hfin g : (Fin 4 → ℝ) → ℝ) v)) =ᵐ[shellMeasure]
      (halfSpace origin ∆ halfSpace (conjAct g origin)).indicator 1 := by
    filter_upwards [coeFn_wallCocycle hfin g] with v hv
    rw [hv, Real.inner_apply]
    by_cases hO : v ∈ halfSpace origin <;> by_cases hX : v ∈ halfSpace (conjAct g origin) <;>
      simp [Set.indicator_apply, Set.mem_symmDiff, hO, hX]
  rw [integral_congr_ae hae, integral_indicator_one hsep]
  rfl

/-- **The wall action**, with translation part scaled by `c`. -/
def wallAction (hfin : SeparationFinite) (c : ℝ) :
    Haagerup.AffineAction.{0, 0} (GL (Fin 2) ℂ) where
  E := Lp ℝ 2 shellMeasure
  π := koopman
  b g := c • wallCocycle hfin g
  isCocycle g h := by
    show c • wallCocycle hfin (g * h) = c • wallCocycle hfin g + koopman g (c • wallCocycle hfin h)
    rw [isCocycle_wallCocycle hfin g h, smul_add, map_smul]

theorem wallAction_b (hfin : SeparationFinite) (c : ℝ) (g : GL (Fin 2) ℂ) :
    (wallAction hfin c).b g = c • wallCocycle hfin g :=
  rfl

end

end Walls
end GHW

/-- **Pulling an affine action back along a homomorphism.** -/
def Haagerup.AffineAction.comapHom {G Γ : Type} [Group G] [Group Γ]
    (A : Haagerup.AffineAction.{0, 0} G) (ρ : Γ →* G) : Haagerup.AffineAction.{0, 0} Γ where
  E := A.E
  π := A.π.comp ρ
  b γ := A.b (ρ γ)
  isCocycle γ δ := by
    show A.b (ρ (γ * δ)) = A.b (ρ γ) + A.π (ρ γ) (A.b (ρ δ))
    rw [map_mul]
    exact A.isCocycle (ρ γ) (ρ δ)

theorem Haagerup.AffineAction.comapHom_b {G Γ : Type} [Group G] [Group Γ]
    (A : Haagerup.AffineAction.{0, 0} G) (ρ : Γ →* G) (γ : Γ) :
    (A.comapHom ρ).b γ = A.b (ρ γ) :=
  rfl

end GroupApproximation

#audit_axioms GroupApproximation.GHW.Walls.conjAct_preimage_halfSpace
#audit_axioms GroupApproximation.GHW.Walls.koopmanEquiv_mul
#audit_axioms GroupApproximation.GHW.Walls.koopman
#audit_axioms GroupApproximation.GHW.Walls.isCocycle_wallCocycle
#audit_axioms GroupApproximation.GHW.Walls.norm_wallCocycle_sq
#audit_axioms GroupApproximation.GHW.Walls.wallAction
#audit_axioms GroupApproximation.Haagerup.AffineAction.comapHom
