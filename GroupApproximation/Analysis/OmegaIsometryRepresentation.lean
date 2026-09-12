import GroupApproximation.Analysis.OmegaCommutatorFixes
import GroupApproximation.Sofic.KOmegaHilbert

/-!
# `π` as a bundled unitary representation on `K_ω`

`CollapseDelormeEndpoint.collapse_contradiction_of_hasKazhdanPropertyT` consumes
a representation in the bundled form

`π : L →* (E ≃ₗᵢ[ℂ] E)`,

while the action built in `Sofic/OmegaOperatorUltraproduct.lean` is
`omegaAct`, a ring homomorphism into `Module.End ℂ (Vec Y w ω)`.  Nothing there
is a linear *isometry equivalence*: the inverse is not exhibited, and no norm is
mentioned, `Vec` carrying none.  This file closes that gap for the action of
`π(g) = [Ad U_n(g)]_ω`, so that the ultraproduct representation drops into the
collapse endpoint with no change on its side.

## Why norm preservation is exact here

For a general unitary of `B_ω` the estimate would have to be run through the
corona norm, because a unitary of a quotient C-star algebra need not lift to a
coordinatewise unitary and only `lim_ω ‖a_n‖ = 1` is available.  For the
representation the manuscript actually forms there is nothing to estimate: the
class `π(g)` has the *coordinatewise unitary* representative
`Ad U_n(g)` (`OmegaAlmostRepresentation.adSeq`, unitary at every stage by
`adSeq_star_mul`), it acts on representatives by `ξ_n ↦ U_n(g) ξ_n U_n(g)*`
(`OmegaCommutatorFixes.applyFam_adSeq`), and unitary conjugation preserves
`matMass` on the nose (`kt_01_matMass_adjoint`).  So the coordinate masses are
*equal*, not merely comparable, and `norm_actK` is an equality of ultralimits.

The norm lives on `KOmega`, the opaque synonym of `Vec` that carries the
inner-product structure, so everything below is stated there.
-/

namespace GroupApproximation
namespace OmegaIsometryRepresentation

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction
open OmegaOperatorUltraproduct OmegaConjugationOperators
open HilbertUltraproductInner KOmegaHilbert
open ScaledKazhdanTransport UltraproductScaledTransport
-- `adSeq` lands in `BoundedMatrixSequence`, which is `lp` over the matrix
-- algebras; its structure needs the matrix norm in scope.
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {H : Type u} [Group H] (A : OpAlmostRepresentation H) (w : ℕ → ℝ)
  (ω : Ultrafilter ℕ)

/-- The action of `π(g) = [Ad U_n(g)]_ω` on `K_ω`, typed as an endomorphism of
`KOmega` rather than of its underlying quotient. -/
def actK (hw : ∀ n, 0 ≤ w n) (g : H) :
    KOmega A.model w ω hw →ₗ[ℂ] KOmega A.model w ω hw :=
  omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)

/-- **`π(g)` is norm preserving.**  The coordinate masses are equal, because the
representative is coordinatewise unitary and unitary conjugation preserves
`matMass` exactly. -/
theorem norm_actK (hw : ∀ n, 0 ≤ w n) (g : H) (x : KOmega A.model w ω hw) :
    ‖actK A w ω hw g x‖ = ‖x‖ := by
  obtain ⟨ξ, hξ⟩ : ∃ ξ : massBounded A.model w, mkK A.model w ω hw ξ = x :=
    Submodule.Quotient.mk_surjective (nullIn A.model w ω)
      (show Vec A.model w ω from x)
  subst hξ
  have hval : actK A w ω hw g (mkK A.model w ω hw ξ)
      = mkK A.model w ω hw
        (actSub A.model w (OmegaAlmostRepresentation.adSeq A g) ξ) := by
    show omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
        (Submodule.Quotient.mk ξ)
      = Submodule.Quotient.mk
        (actSub A.model w (OmegaAlmostRepresentation.adSeq A g) ξ)
    rw [OmegaAlmostRepresentation.piOmega_def, omegaAct_omegaMk, actQ_mk]
  rw [hval, norm_mkK, norm_mkK]
  congr 1
  refine ulim_congr (Eventually.of_forall fun n ↦ ?_)
    (exists_tendsto_mass hw _)
  show matMass ((actSub A.model w (OmegaAlmostRepresentation.adSeq A g) ξ :
        MatFam A.model) n) / w n
      = matMass ((ξ : MatFam A.model) n) / w n
  rw [actSub_coe]
  simp only [OmegaCommutatorFixes.applyFam_adSeq]
  rw [kt_01_matMass_adjoint (A.map n g).2]

/-! ## The inverse, and the bundled equivalence -/

/-! `hω` is passed as an explicit binder rather than carried as a section
variable: it is used only inside the proofs below, and a section hypothesis that
no statement mentions is not auto-included by the elaborator. -/

theorem actK_comp_inv (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hw : ∀ n, 0 ≤ w n) (g : H) :
    (actK A w ω hw g).comp (actK A w ω hw g⁻¹) = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  show omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
      (omegaAct A.model w ω hw
        (OmegaAlmostRepresentation.piOmega A ω g⁻¹) x) = x
  rw [← omegaAct_mul, ← OmegaAlmostRepresentation.piOmega_mul A ω hω,
    mul_inv_cancel, OmegaAlmostRepresentation.piOmega_one A ω hω, omegaAct_one]

theorem actK_inv_comp (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hw : ∀ n, 0 ≤ w n) (g : H) :
    (actK A w ω hw g⁻¹).comp (actK A w ω hw g) = LinearMap.id := by
  refine LinearMap.ext fun x ↦ ?_
  show omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g⁻¹)
      (omegaAct A.model w ω hw
        (OmegaAlmostRepresentation.piOmega A ω g) x) = x
  rw [← omegaAct_mul, ← OmegaAlmostRepresentation.piOmega_mul A ω hω,
    inv_mul_cancel, OmegaAlmostRepresentation.piOmega_one A ω hω, omegaAct_one]

/-- **`π(g)` as a unitary of `K_ω`**: linear, invertible with inverse `π(g⁻¹)`,
and norm preserving. -/
def repEquiv (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hw : ∀ n, 0 ≤ w n) (g : H) :
    KOmega A.model w ω hw ≃ₗᵢ[ℂ] KOmega A.model w ω hw where
  toLinearEquiv := LinearEquiv.ofLinear (actK A w ω hw g) (actK A w ω hw g⁻¹)
    (actK_comp_inv A w ω hω hw g) (actK_inv_comp A w ω hω hw g)
  norm_map' := norm_actK A w ω hw g

/-- **The ultraproduct representation, bundled.**  `π(g) = [Ad U_n(g)]_ω` as a
homomorphism into the unitary group of `K_ω`, in exactly the shape
`collapse_contradiction_of_hasKazhdanPropertyT` consumes.

The hypothesis `hω` is the manuscript's own: `ω` is free.  It is what makes an
operator-norm *almost* representation into an honest homomorphism in the
ultraproduct, and it enters only through `piOmega_mul` and `piOmega_one`. -/
def rep (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (hw : ∀ n, 0 ≤ w n) :
    H →* (KOmega A.model w ω hw ≃ₗᵢ[ℂ] KOmega A.model w ω hw) where
  toFun g := repEquiv A w ω hω hw g
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    show omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω 1) x = x
    rw [OmegaAlmostRepresentation.piOmega_one A ω hω, omegaAct_one]
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    show omegaAct A.model w ω hw
        (OmegaAlmostRepresentation.piOmega A ω (g * h)) x
      = omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
          (omegaAct A.model w ω hw
            (OmegaAlmostRepresentation.piOmega A ω h) x)
    rw [OmegaAlmostRepresentation.piOmega_mul A ω hω, omegaAct_mul]

@[simp] theorem rep_apply (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hw : ∀ n, 0 ≤ w n) (g : H)
    (x : KOmega A.model w ω hw) :
    rep A w ω hω hw g x = actK A w ω hw g x := rfl

end

end OmegaIsometryRepresentation
end GroupApproximation
