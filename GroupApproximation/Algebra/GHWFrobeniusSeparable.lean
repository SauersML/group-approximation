import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.CharP.IntermediateField
import GroupApproximation.Meta.AxiomGuard

/-!
# A power of Frobenius maps a finite extension into its separable closure

This is step (4) of the proof of the sentence "Every countable subgroup of $\mathrm{GL}_2$ over a
field has the Haagerup property~\cite[Theorem~4]{GHW}" (`non_mf_groups_exist.tex`, tex lines
1146--1147). The step is proved here, not cited.

Let `K / L` be a finite extension and `p` the exponential characteristic of `L`. The separable
closure `K' = separableClosure L K` of `L` in `K` is separable over `L`. The extension `K / K'` is
purely inseparable and finite, so it has an exponent `e`: every `x : K` satisfies `x ^ p ^ e ∈ K'`.
So the iterated Frobenius `x ↦ x ^ p ^ e` is a ring homomorphism `K →+* K'`.

* `GroupApproximation.GHW.exists_separable_frobenius_embedding`
-/

namespace GroupApproximation
namespace GHW

/-- Let `K / L` be a finite extension of exponential characteristic `p`. A ring homomorphism acting
as `x ↦ x ^ p ^ e` maps `K` into a separable intermediate field `K'`. Here `K'` is the separable
closure of `L` in `K`, `e` is the exponent of the purely inseparable extension `K / K'`, and the map
is `IsPurelyInseparable.iterateFrobenius`. -/
theorem exists_separable_frobenius_embedding (L K : Type*) [Field L] [Field K] [Algebra L K]
    [FiniteDimensional L K] (p : ℕ) [ExpChar L p] :
    ∃ (K' : IntermediateField L K) (e : ℕ) (φ : K →+* K'),
      Algebra.IsSeparable L K' ∧ ∀ x : K, ((φ x : K') : K) = x ^ p ^ e :=
  ⟨separableClosure L K, IsPurelyInseparable.exponent (separableClosure L K) K,
    IsPurelyInseparable.iterateFrobenius (separableClosure L K) K p le_rfl, inferInstance,
    fun x ↦ IsPurelyInseparable.algebraMap_iterateFrobenius (separableClosure L K) p le_rfl x⟩

#audit_axioms GroupApproximation.GHW.exists_separable_frobenius_embedding

end GHW
end GroupApproximation
