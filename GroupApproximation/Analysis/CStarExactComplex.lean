import GroupApproximation.Analysis.CStarMinTensorQuotient
import GroupApproximation.Analysis.CStarIdealQuotient

/-!
# The scalars are exact

## What this module builds

`CStarMinTensorQuotient.IsExactCStar` states exactness of a C⋆-algebra in the
kernel form: for every closed star-stable two-sided ideal `I` of every unital
C⋆-algebra `B`, the kernel of `(B ⧸ I) ⊗_min C ← B ⊗_min C` is exactly the
closure of `I ⊙ C`.  When that predicate was written, no algebra was known to
satisfy it in this development -- the definition existed so that the
manuscript's exactness sentence would be *statable*.  A predicate with no
instance certifies nothing, so this module supplies one:

* `norm_quotientMinTensorMap_le` -- the quotient map on minimal tensor
  products is contractive (true on the dense algebraic part by the
  functoriality inequality, and `‖f z‖ ≤ ‖z‖` is a closed condition);
* `isExactCStar_complex` -- **`ℂ` is exact**.

## The proof

`B ⊗_min ℂ` is `B`: every algebraic tensor is `b ⊗ₜ 1` (`TensorProduct.rid`)
and `‖b ⊗ₜ 1‖ = ‖b‖` by the cross-norm identity.  So an element `z` of the
kernel is approximated by some `b ⊗ₜ 1`, and contractivity of the quotient map
turns "the image of `z` is `0`" into "the coset of `b` is small".  A
representative `r` of that coset with `‖r‖` within `ε/3` of the coset norm
(`quotient_norm_mk_lt`) puts `b - r` in `I`, and `(b - r) ⊗ₜ 1` is within `ε`
of `z`.  Everything is `ε/3`-bookkeeping; no approximate unit and no state is
needed, because the second factor contributes only the scalar `1`.

## What is claimed and what is not

This is a non-vacuity theorem, not progress on `SO.16`.  Exactness of
`C⋆_red(E)` is a theorem about a highly non-commutative algebra and needs the
Kirchberg--Wassermann crossover, of which nothing here is an instance.  What
the module does establish is that the tree's exactness predicate is the
textbook one in at least the sense that the textbook's trivial example
satisfies it -- a definition that no algebra satisfied would be evidence that
the predicate was mis-stated.

## Manuscript status

Infrastructure.  `SO.16` keeps its grade.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct

universe u v

/-! ## Contractivity of the quotient map -/

/-- **The quotient map on minimal tensor products is contractive.**  On the
dense algebraic part this is the functoriality inequality for a surjective
⋆-homomorphism; `{z | ‖f z‖ ≤ ‖z‖}` is closed and `f` is continuous. -/
theorem norm_quotientMinTensorMap_le
    {B : Type u} {C : Type v} [CStarAlgebra B] [CStarAlgebra C]
    [Nontrivial B] [Nontrivial C]
    (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
    [Nontrivial (B ⧸ I)] (z : MinTensorProduct B C) :
    ‖quotientMinTensorMap I z‖ ≤ ‖z‖ := by
  have hcont : Continuous (quotientMinTensorMap I) :=
    UniformSpace.Completion.continuous_extension
      (f := ((minPreQuotientMap I :
          MinPreTensor B C →⋆ₐ[ℂ] MinTensorProduct (B ⧸ I) C) :
        MinPreTensor B C → MinTensorProduct (B ⧸ I) C))
  refine (denseRange_minTensorIn (A := B) (B := C)).induction_on z ?_ ?_
  · exact isClosed_le (continuous_norm.comp hcont) continuous_norm
  · intro x
    rw [quotientMinTensorMap_minTensorIn, norm_minTensorIn, norm_minTensorIn,
      tensorStarAlgHomMap_apply]
    exact minTensorNorm_map_le (quotientStarMk I) (quotientStarMk_surjective I) x

/-! ## The scalars are exact -/

/-- **`ℂ` is exact.**  For every closed star-stable two-sided ideal `I` of
every unital C⋆-algebra `B`, an element of `B ⊗_min ℂ` killed by the quotient
map lies in the closure of `I ⊙ ℂ`.

The first instance of `IsExactCStar` in this development. -/
theorem isExactCStar_complex : IsExactCStar ℂ := by
  intro B hB hBnt I hI2 hIst hIcl hQnt z hz
  letI := hB
  letI := hBnt
  letI := hI2
  letI := hIst
  letI := hIcl
  letI := hQnt
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- Approximate `z` by an algebraic tensor, and put it in the form `b ⊗ₜ 1`.
  obtain ⟨w, hwmem, hwdist⟩ :=
    Metric.mem_closure_iff.mp
      (denseRange_minTensorIn (A := B) (B := ℂ) z) (ε / 3) hε3
  obtain ⟨x, rfl⟩ := hwmem
  obtain ⟨b, rfl⟩ : ∃ b : B, x = b ⊗ₜ[ℂ] (1 : ℂ) :=
    ⟨(TensorProduct.rid ℂ B) x, by
      rw [← TensorProduct.rid_symm_apply, LinearEquiv.symm_apply_apply]⟩
  -- The coset of `b` is small: the quotient map is contractive and kills `z`.
  have hq : ‖(Ideal.Quotient.mk I b : B ⧸ I)‖ < ε / 3 := by
    have h1 : quotientMinTensorMap I (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)))
        = minTensorIn (B ⧸ I) ℂ ((Ideal.Quotient.mk I b) ⊗ₜ[ℂ] (1 : ℂ)) := by
      rw [quotientMinTensorMap_minTensorIn]
      exact congrArg (minTensorIn (B ⧸ I) ℂ)
        (Algebra.TensorProduct.map_tmul (quotientStarMk I).toAlgHom
          (AlgHom.id ℂ ℂ) b (1 : ℂ))
    have h2 : ‖(Ideal.Quotient.mk I b : B ⧸ I)‖
        = ‖quotientMinTensorMap I (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)))‖ := by
      rw [h1, norm_minTensorIn_tmul, norm_one, mul_one]
    have h3 : quotientMinTensorMap I (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)))
        = quotientMinTensorMap I
            (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)) - z) := by
      rw [map_sub, hz, sub_zero]
    have h4 : ‖minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)) - z‖ < ε / 3 := by
      rw [← dist_eq_norm, dist_comm]
      exact hwdist
    rw [h2, h3]
    exact lt_of_le_of_lt (norm_quotientMinTensorMap_le I _) h4
  -- A representative of that coset, and the ideal element it produces.
  obtain ⟨r, hr, hrnorm⟩ :=
    quotient_norm_mk_lt I (Ideal.Quotient.mk I b) hε3
  have hmem : b - r ∈ I := by
    have h0 : Ideal.Quotient.mk I (b - r) = 0 := by
      rw [map_sub, hr, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  refine ⟨minTensorIn B ℂ ((b - r) ⊗ₜ[ℂ] (1 : ℂ)),
    Submodule.subset_span ⟨b - r, (1 : ℂ), hmem, rfl⟩, ?_⟩
  have hsub : minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ))
        - minTensorIn B ℂ ((b - r) ⊗ₜ[ℂ] (1 : ℂ))
      = minTensorIn B ℂ (r ⊗ₜ[ℂ] (1 : ℂ)) := by
    rw [← map_sub, ← TensorProduct.sub_tmul, sub_sub_cancel]
  have hdist2 : dist (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)))
      (minTensorIn B ℂ ((b - r) ⊗ₜ[ℂ] (1 : ℂ))) = ‖r‖ := by
    rw [dist_eq_norm, hsub, norm_minTensorIn_tmul, norm_one, mul_one]
  calc dist z (minTensorIn B ℂ ((b - r) ⊗ₜ[ℂ] (1 : ℂ)))
      ≤ dist z (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)))
          + dist (minTensorIn B ℂ (b ⊗ₜ[ℂ] (1 : ℂ)))
            (minTensorIn B ℂ ((b - r) ⊗ₜ[ℂ] (1 : ℂ))) :=
        dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        refine add_lt_add hwdist ?_
        rw [hdist2]
        linarith
    _ = ε := by ring

end CStarTensor
end GroupApproximation
