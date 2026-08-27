import GroupApproximation.Analysis.CollapseUltraproductRepresentation
import GroupApproximation.Analysis.OmegaIsometryRepresentation

/-!
# The corona action and the conjugation action are the same map

Two representations of a group on `K_ω` have been built independently, and the
two halves of `CO.21b` are stated against different ones:

* `CollapseUltraproductRepresentation.conjRep`, conjugation by a coordinatewise
  unitary family, which is what `collapse_contradiction_kOmega` consumes;
* `omegaAct ∘ OmegaAlmostRepresentation.piOmega`, the action of the norm
  ultraproduct `B_ω`, which is what the fixed-space results
  (`OmegaConjugationOperators`, `OmegaFixRange`) are stated about.

They are different *objects* -- one is defined through the corona quotient and
the doubled index, the other directly on representatives -- so no citation
typechecks across them, and that is the only thing still separating the two
halves.  They are, however, the same *map*: both send `[ξ_n]_ω` to
`[U_n ξ_n U_n*]_ω`.  This file proves that.

## The three statements

* `omegaAct_piOmega_eq_conjQ` -- the identification at the level of linear maps
  of `K_ω`.  Both sides are computed on a representative: the corona side
  through `applyFam_adSeq`, which says the doubled matrix `conjDouble U_n` acts
  on row-major coordinates by conjugation, and the conjugation side by
  definition.
* `repEquiv_eq_conjIsometryEquiv` -- the same, bundled, so that the isometry
  equivalences agree and not merely their underlying maps.
* `rep_strictRep_eq_conjRep` -- the same at the level of the homomorphism, for a
  strictly multiplicative coordinate lift `Θ`, which is the hypothesis
  `collapse_contradiction_kOmega` is stated with.

`strictRep` is the observation that makes the last one typecheck: a strictly
multiplicative `Θ` *is* an operator-norm almost representation, with defect
exactly `0` rather than merely vanishing, so the corona machinery applies to it
verbatim.
-/

namespace GroupApproximation
namespace OmegaConjQCompatibility

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open CollapseCocycleAnalytic
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {H : Type u} [Group H]

/-! ## The identification, on linear maps -/

/-- **The corona action is the conjugation action.**  `π(g) = [Ad U_n(g)]_ω`
acting through `B_ω` on `K_ω` is the map `conjQ` induced by conjugating
representatives by `U_n(g)`. -/
theorem omegaAct_piOmega_eq_conjQ (A : OpAlmostRepresentation H) (w : ℕ → ℝ)
    (ω : Ultrafilter ℕ) (hw : ∀ n, 0 ≤ w n) (g : H) :
    omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
      = conjQ A.model w ω (fun n ↦ A.map n g) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn A.model w ω) x
  have hfam : actSub A.model w (OmegaAlmostRepresentation.adSeq A g) ξ
      = conjBounded A.model w (fun n ↦ A.map n g) ξ := by
    refine Subtype.ext (funext fun n ↦ ?_)
    rw [actSub_coe]
    exact congrFun
      (OmegaCommutatorFixes.applyFam_adSeq A g (ξ : MatFam A.model)) n
  rw [OmegaAlmostRepresentation.piOmega_def, omegaAct_omegaMk, actQ_mk,
    conjQ_mk, hfam]

/-! ## The identification, bundled -/

/-- The two bundled unitaries of `K_ω` agree. -/
theorem repEquiv_eq_conjIsometryEquiv (A : OpAlmostRepresentation H)
    (w : ℕ → ℝ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (hw : ∀ n, 0 ≤ w n) (g : H) :
    OmegaIsometryRepresentation.repEquiv A w ω hω hw g
      = CollapseUltraproductRepresentation.conjIsometryEquiv A.model w ω hw
          (fun n ↦ A.map n g) := by
  apply LinearIsometryEquiv.ext
  intro x
  show omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g) x
    = conjQ A.model w ω (fun n ↦ A.map n g) x
  rw [omegaAct_piOmega_eq_conjQ]

/-! ## A strictly multiplicative lift is an almost representation -/

section Strict

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-- **A strictly multiplicative coordinate lift, as an operator-norm almost
representation.**  Its multiplicative defect is not merely vanishing but
identically zero, so every hypothesis is discharged at `N = 0`. -/
def strictRep (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) :
    OpAlmostRepresentation H where
  model := Y
  modelNonempty n := Fintype.card_pos
  map n g := Θ g n
  asymptoticallyMultiplicative g h ε hε := by
    refine ⟨0, fun n _ ↦ ?_⟩
    have hmul : Θ (g * h) n = Θ g n * Θ h n :=
      congrArg (fun V : (∀ m, Matrix.unitaryGroup (Y m) ℂ) ↦ V n)
        (map_mul Θ g h)
    rw [hmul, Submonoid.coe_mul, sub_self, norm_zero]
    exact hε.le

@[simp] theorem strictRep_model (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) :
    (strictRep Y Θ).model = Y := rfl

@[simp] theorem strictRep_map (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (n : ℕ) (g : H) : (strictRep Y Θ).map n g = Θ g n := rfl

/-- **The two representations are one homomorphism.**  For a strictly
multiplicative lift `Θ`, the bundled corona representation of
`Analysis/OmegaIsometryRepresentation.lean` *is*
`CollapseUltraproductRepresentation.conjRep`.

This is what lets the fixed-space results, which are stated for the corona
action, be cited against `collapse_contradiction_kOmega`, which is stated for
`conjRep`. -/
theorem rep_strictRep_eq_conjRep (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (w : ℕ → ℝ) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (hw : ∀ n, 0 ≤ w n) :
    OmegaIsometryRepresentation.rep (strictRep Y Θ) w ω hω hw
      = CollapseUltraproductRepresentation.conjRep Y w ω hw Θ := by
  refine MonoidHom.ext fun g ↦ ?_
  refine LinearIsometryEquiv.ext fun x ↦ ?_
  -- Spell the model as `(strictRep Y Θ).model`, not as `Y`: the two are equal
  -- by `rfl` and the ambient `Nonempty` instances are propositionally
  -- irrelevant, so the goal is the same either way -- but `rw` matches
  -- syntactically and only the first spelling is the head of
  -- `omegaAct_piOmega_eq_conjQ`.
  show omegaAct (strictRep Y Θ).model w ω hw
      (OmegaAlmostRepresentation.piOmega (strictRep Y Θ) ω g) x
    = conjQ Y w ω (fun n ↦ Θ g n) x
  rw [omegaAct_piOmega_eq_conjQ (strictRep Y Θ) w ω hw g]
  -- `strictRep_model` and `strictRep_map` are both `rfl`.
  rfl

end Strict

end

end OmegaConjQCompatibility
end GroupApproximation
