import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Manuscript.NonMF.RelatedTWW.Definitions
import GroupApproximation.Meta.AxiomGuard

/-!
# NF ⇒ quasidiagonal (Blackadar--Kirchberg): the reduction to the CP bridge

Lane `nm-intro-09`, `non_mf_groups_exist.tex` L310: a separable NF algebra is
quasidiagonal (Blackadar--Kirchberg).

## Proof route

`IsNFAlgebra.exists_sequenceModel` (`Analysis/NFAlgebra.lean`) does the
dense-sequence diagonalization. It takes a dense sequence `u`, local
approximations on `F_n = {u 0, …, u n}` at tolerance `1/(n+1)`, and a 3ε
argument. The result is completely positive contractions `down n : A → M_{Y_n}`
and `up n : M_{Y_n} → A` with vanishing multiplicative defect and
`‖up n (down n a) - a‖ → 0` for every `a`.

The down maps are the quasidiagonal models `QuasidiagonalModel.map`.

* `norm_le` is the contraction clause of `down`.
* `map_star` is `OrderZero.map_star_of_cp`.
* `tendsto_mul` is the sequence model's clause.
* `limsup_norm` comes from `tendsto_norm_down`, a squeeze:
  `‖a‖ - ‖up n (down n a) - a‖ ≤ ‖up n (down n a)‖ ≤ ‖down n a‖ ≤ ‖a‖`, where
  the middle step is the contraction of `up`. So `‖down n a‖ → ‖a‖`, and the
  limsup of a convergent sequence is its limit.
* `completelyPositive` asks for the form-sense predicate
  `Quasidiagonal.IsCompletelyPositiveOnMatrices`. The model gives the
  factorization-sense `CStarExactness.IsCompletelyPositive`. The passage between
  them is the interface of lane `nm-intro-08`, recorded here as
  `CompletelyPositiveOnMatricesBridgeStatement`.

The bridge is true, and it is strictly smaller in proof content than the target:
it is one field of the model and involves no approximation. It is proved in
`IntroCarto09NFQDBridge` by transport to `B(ℓ²)` and
`LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean`. The closed
endpoint is in `IntroCarto09NFQD`.

The local matrix C⋆-instance is a field-for-field copy of the one in
`Analysis/NFAlgebra.lean`, so the complete-positivity hypotheses of
`NFSequenceModel` unify with the terms elaborated here.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto09

open CStarExactness
open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-- Matrix blocks at the scoped operator norm are C⋆-algebras (the instance of
`Analysis/NFAlgebra.lean`, field for field). -/
local instance matrixBlockCStarAlgebraForIntroCarto09 (Z : Type) [Fintype Z]
    [DecidableEq Z] [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **The CP bridge** (the interface of lane `nm-intro-08`): a completely
positive map into a positive-dimensional matrix block, in the factorization
sense, is completely positive in the entrywise form sense used by
`RelatedTWW.QuasidiagonalModel`.

It is true. Transport along `M_Y ≅ B(ℓ²(Fin |Y|))` keeps complete positivity,
and completely positive operator models are form-positive
(`LocalLifting.isCompletelyPositiveOnMatrices_matrixOfEuclidean`). It is proved
as `IntroCarto09.completelyPositiveOnMatricesBridge`. -/
def CompletelyPositiveOnMatricesBridgeStatement : Prop :=
  ∀ (A : Type u) [CStarAlgebra A] (Y : FiniteModel) [Nonempty Y]
    (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
    IsCompletelyPositive φ → Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑φ

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.CompletelyPositiveOnMatricesBridgeStatement

/-- **Norm recovery of the down maps.** Along an NF sequence model,
`‖down n a‖ → ‖a‖`. The upper bound is the contraction of `down`. The lower
bound is `‖a‖ - ‖up n (down n a) - a‖ ≤ ‖up n (down n a)‖ ≤ ‖down n a‖`. -/
theorem tendsto_norm_down {A : Type u} [CStarAlgebra A]
    {space : ℕ → FiniteModel} [∀ n, Nonempty (space n)]
    (M : NFSequenceModel A space) (a : A) :
    Tendsto (fun n ↦ ‖M.down n a‖) atTop (nhds ‖a‖) := by
  have hlow : Tendsto (fun n ↦ ‖a‖ - ‖M.up n (M.down n a) - a‖) atTop
      (nhds ‖a‖) := by
    simpa only [sub_zero] using (M.tendsto_recovery a).const_sub ‖a‖
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro n
    show ‖a‖ - ‖M.up n (M.down n a) - a‖ ≤ ‖M.down n a‖
    have h1 : ‖a‖ - ‖M.up n (M.down n a)‖ ≤ ‖a - M.up n (M.down n a)‖ :=
      norm_sub_norm_le a (M.up n (M.down n a))
    have h2 : ‖M.up n (M.down n a)‖ ≤ ‖M.down n a‖ :=
      M.upContractive n (M.down n a)
    have h3 : ‖a - M.up n (M.down n a)‖ = ‖M.up n (M.down n a) - a‖ :=
      norm_sub_rev a (M.up n (M.down n a))
    linarith
  · intro n
    show ‖M.down n a‖ ≤ ‖a‖
    exact M.downContractive n a

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.tendsto_norm_down

/-- **NF ⇒ quasidiagonal, modulo the CP bridge.** The down maps of the NF
sequence model of `IsNFAlgebra.exists_sequenceModel` are quasidiagonal matrix
models. -/
theorem isQuasidiagonalCStarAlgebra_of_isNFAlgebra_of_cpBridge
    (hbridge : CompletelyPositiveOnMatricesBridgeStatement.{u})
    {A : Type u} [CStarAlgebra A] (hA : IsNFAlgebra A) :
    RelatedTWW.IsQuasidiagonalCStarAlgebra A := by
  obtain ⟨space, hne, ⟨M⟩⟩ := hA.exists_sequenceModel
  letI : ∀ n, Nonempty (space n) := hne
  refine ⟨hA.separable, ⟨{
    space := space
    nonempty := hne
    map := M.down
    completelyPositive := fun n ↦
      hbridge A (space n) (M.down n) (M.downCompletelyPositive n)
    norm_le := M.downContractive
    map_star := fun n a ↦
      (OrderZero.map_star_of_cp (M.downCompletelyPositive n) a).trans
        (Matrix.star_eq_conjTranspose (M.down n a))
    tendsto_mul := M.tendsto_mul
    limsup_norm := fun a ↦ (tendsto_norm_down M a).limsup_eq }⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto09.isQuasidiagonalCStarAlgebra_of_isNFAlgebra_of_cpBridge

end

end IntroCarto09
end NonMF
end Manuscript
end GroupApproximation
