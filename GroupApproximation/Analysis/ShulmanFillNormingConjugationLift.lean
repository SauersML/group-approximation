import GroupApproximation.Analysis.ShulmanFillNormingConjugation

/-!
# The conjugated asymptotic lift

`Analysis/ShulmanFillNormingConjugation` collects the algebra of conjugation by
a unitary `U` of `𝒟`.  This module assembles it: `conjugate` turns an
asymptotic lift of `π` into an asymptotic lift of `Ad (q U) ∘ π`, with every
defect bounded by the corresponding defect of the original.

That is Shulman's Lemma 9 in the vocabulary that survives
`Analysis/ShulmanFillNormingResiduallyFinite`, and it is exact: the paper needs
a Halmos dilation only because its decoupling unitary lives in `M₄(𝒟)` and
merely converges to the flip, whereas a unitary of `𝒟` conjugates on the nose.

## What Theorem 10 still needs on top of this

Two things, neither of them an estimate.

* **The flip as a unitary of `𝒟`.**  For the symmetric double the decoupling
  unitary is `((0,1),(1,0))` over the models, so `U` exists as soon as the
  models are `M₂` over something and `H` is a twofold block space
  `PiLp 2 (fun _ : Fin 2 ↦ H₀)`; the pattern is
  `Analysis/LanceBlockOperator`, and the exact commutation with the diagonal
  image of `C` is `ShulmanFill.flip2_commutes_diagonal2_self`.  With that `U`,
  `conjugate` produces the second leg `φ⁽¹⁾ = U φ⁽²⁾ U*` of the paper's proof
  from the first, and the two agree on `C` *exactly*, not asymptotically,
  because the flip commutes with `diag(x, x)`.
* **Lemma 7, the gluing** — two asymptotic lifts of `D` agreeing on `C` glue to
  one asymptotic lift of `D *_C D`.  The corona-valued special case is
  `MFAlgebraAmalgamCriterion.exists_compatible_asymptotic_amalgam_model`; the
  `𝒟`-valued one is not in the repository.

And above both, the input this whole lane is waiting on:

**(Theorem 4, lifting direction.)**  For every twofold block model
`(ι, hnorm, hone)` with `∀ n, HasMFEmbedding (A n)`, every separable MF `B`
and every faithful `π : B →⋆ₐ[ℂ] (H →L[ℂ] H)`,
`Nonempty (ShulmanFill.StarStrongAsymptoticLift ι hnorm hone π)`.

That is Blackadar--Kirchberg's equivalence between corona embeddability and the
matricial-field property; its every-representation form needs Voiculescu-type
absorption.  It is carried as an explicit binder wherever it is consumed, never
as a `Prop` definition, so that a consumer's type names it.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

section Conjugate

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)]
-- `lp _ ∞` is a unital ring only when its factors are, so the `𝒟` API now
-- carries this; `StarStrongLimitNorm` declares it the same way.
variable [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type v} [CStarAlgebra B]
variable {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

variable (U : StarStrong.BoundedStarSequence A)
  (hUmem : U ∈ StarStrong.starStrongSubalgebra ι hnorm hone)
  (hUl : star U * U = 1) (hUr : U * star U = 1) (hU1 : ‖U‖ ≤ 1)

namespace StarStrongAsymptoticLift

/-- **Lemma 9 inside `𝒟`.**  Conjugating an asymptotic lift of `π` by a unitary
`U` of `𝒟` gives an asymptotic lift of `Ad (q U) ∘ π`.  Every defect is
conjugated verbatim, and conjugation by a contraction and its adjoint cannot
enlarge a norm, so each new defect is bounded by the old one; the lifting
clause moves by `q U` because `q` is a unital `*`-homomorphism.

`unitaryConj` is given its carrier explicitly: left implicit, `unitary ?D` sets
off a search for `CStarAlgebra ?D` with `?D` unknown, and that search does not
finish inside the heartbeat budget. -/
def conjugate (φ : StarStrongAsymptoticLift ι hnorm hone π) :
    StarStrongAsymptoticLift ι hnorm hone
      ((unitaryConj (D := H →L[ℂ] H)
        (limitUnitaryBundled U hUmem hUl hUr)).comp π) where
  toFun t b := U * φ.toFun t b * star U
  mem t b := mul_mem (mul_mem hUmem (φ.mem t b)) (star_mem hUmem)
  norm_le t b := (norm_conj_le U hU1 (φ.toFun t b)).trans (φ.norm_le t b)
  tendsto_add b c := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_)
      (φ.tendsto_add b c)
    rw [conj_sub_sub]
    exact norm_conj_le U hU1 _
  tendsto_smul z b := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_)
      (φ.tendsto_smul z b)
    rw [conj_smul, conj_sub]
    exact norm_conj_le U hU1 _
  tendsto_mul b c := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_)
      (φ.tendsto_mul b c)
    rw [conj_mul U hUl, conj_sub]
    exact norm_conj_le U hU1 _
  tendsto_star b := by
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_)
      (φ.tendsto_star b)
    rw [conj_star, conj_sub]
    exact norm_conj_le U hU1 _
  tendsto_one := by
    -- `U 1 U* = U U* = 1`, so the conjugated unitality defect is the
    -- conjugate of the original one.
    refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_) φ.tendsto_one
    have h1 : U * φ.toFun t (1 : B) * star U - 1
        = U * (φ.toFun t (1 : B) - 1) * star U := by
      rw [← conj_sub U (φ.toFun t (1 : B)) 1, mul_one, hUr]
    rw [h1]
    exact norm_conj_le U hU1 _
  lift t b := by
    have hsub : (⟨U * φ.toFun t b * star U,
        mul_mem (mul_mem hUmem (φ.mem t b)) (star_mem hUmem)⟩ :
          StarStrong.starStrongSubalgebra ι hnorm hone) =
        ⟨U, hUmem⟩ * ⟨φ.toFun t b, φ.mem t b⟩ * star ⟨U, hUmem⟩ :=
      Subtype.ext rfl
    rw [hsub, map_mul, map_mul, map_star, φ.lift t b]
    rfl

@[simp] theorem conjugate_toFun (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (t : ℕ) (b : B) :
    (conjugate U hUmem hUl hUr hU1 φ).toFun t b =
      U * φ.toFun t b * star U := rfl

/-- Conjugation by a unitary commuting with the image of a subalgebra changes
nothing there.  This is why the two legs of the symmetric double agree on `C`
*exactly*: the flip commutes with `diag(x, x)`, and `conjugate` inherits that
commutation coordinatewise. -/
theorem conjugate_toFun_eq_of_commute
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (t : ℕ) (b : B)
    (hcomm : U * φ.toFun t b = φ.toFun t b * U) :
    (conjugate U hUmem hUl hUr hU1 φ).toFun t b = φ.toFun t b := by
  show U * φ.toFun t b * star U = φ.toFun t b
  rw [hcomm, mul_assoc, hUr, mul_one]

end StarStrongAsymptoticLift

end Conjugate

end

end ShulmanFill
end GroupApproximation
