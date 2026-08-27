import GroupApproximation.Higman.OmegaTowerSelectedSignedFactors

/-!
# Recovering a common right tail from the low-row factor

The indexed normal form remembers every coordinate below the cutoff and
forgets exactly the right tail.  These lemmas turn equality in its left free
factor into the literal additive decomposition used by the corrected fourth
canonical return case.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- Restore a retained low-row index to the original integer alphabet. -/
def lowRowFactorRestore (m : ℕ) :
    FreeGroup (LowIndex m) →* FreeGroup ℤ :=
  FreeGroup.map fun i => (i : ℤ)

theorem lowRowFactorRestore_comp_lowRowFactor (m : ℕ) :
    (lowRowFactorRestore m).comp (lowRowFactor m) =
      Split.killOn (fun i : ℤ => i < (m : ℤ)) := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  by_cases hi : i < (m : ℤ)
  · simp [lowRowFactorRestore, lowRowFactor, Split.killOn_of, hi]
  · simp [lowRowFactorRestore, lowRowFactor, Split.killOn_of, hi]

/-- Equality of low-row factors is exactly equality of the sequence
coordinates strictly below the cutoff. -/
theorem lowPart_eq_of_lowRowFactor_elt_eq
    {m : ℕ} {l f : E}
    (hEq : lowRowFactor m (elt l) = lowRowFactor m (elt f)) :
    Finsupp.filter (fun i : ℤ => i < (m : ℤ)) l =
      Finsupp.filter (fun i : ℤ => i < (m : ℤ)) f := by
  apply elt_injective
  have hmap := congrArg (lowRowFactorRestore m) hEq
  rw [← MonoidHom.comp_apply, lowRowFactorRestore_comp_lowRowFactor,
    Split.killOn_elt, ← MonoidHom.comp_apply,
    lowRowFactorRestore_comp_lowRowFactor, Split.killOn_elt] at hmap
  exact hmap

/-- A sequence with the same low-row factor as a legal window block is that
block followed by a uniquely determined right-tail sequence. -/
theorem exists_rightTail_add_of_lowRowFactor_eq
    {m : ℕ} {beta l : E}
    (hEq : lowRowFactor m (elt l) = lowRowFactor m (elt beta)) :
    ∃ t : E, rightTailSet m t ∧ l = beta + t := by
  let t : E := l - beta
  have hlow := lowPart_eq_of_lowRowFactor_elt_eq hEq
  refine ⟨t, ?_, ?_⟩
  · intro i hi
    by_contra him
    have hiLow : i < (m : ℤ) := lt_of_not_ge him
    have hcoord := congrArg (fun q : E => q i) hlow
    have hcoord' : l i = beta i := by
      simpa [Finsupp.filter_apply, hiLow] using hcoord
    have htZero : t i = 0 := by
      simp [t, hcoord']
    exact hi htZero
  · simp [t]

/-- The increasing row word of a window block followed by a right tail is
the product of the corresponding `K` basis elements. -/
theorem bK_add_rightTail {m : ℕ} {beta t : E}
    (hbeta : beta ∈ blockSet m) (ht : rightTailSet m t) :
    bK (beta + t) = bK beta * bK t := by
  apply Subtype.ext
  exact bElt_add_rightTail hbeta ht

/-- Cancellation in the intrinsic row equation identifies the two tails in
the two-nonzero-letter return case. -/
theorem rightTail_eq_of_bK_pair_equation
    {m : ℕ} {beta gamma t u : E}
    (hbeta : beta ∈ blockSet m) (hgamma : gamma ∈ blockSet m)
    (ht : rightTailSet m t) (hu : rightTailSet m u)
    (hEq : bK beta * (bK gamma)⁻¹ =
      bK (beta + t) * (bK (gamma + u))⁻¹) :
    t = u := by
  have hEq' : bK beta * (bK gamma)⁻¹ =
      bK beta * ((bK t * (bK u)⁻¹) * (bK gamma)⁻¹) := by
    calc
      bK beta * (bK gamma)⁻¹ =
          bK (beta + t) * (bK (gamma + u))⁻¹ := hEq
      _ = bK beta * ((bK t * (bK u)⁻¹) * (bK gamma)⁻¹) := by
        rw [bK_add_rightTail hbeta ht, bK_add_rightTail hgamma hu]
        group
  have hcancelLeft : (bK gamma)⁻¹ =
      (bK t * (bK u)⁻¹) * (bK gamma)⁻¹ := by
    exact mul_left_cancel hEq'
  have hcancelRight : (1 : ↥Conj.K) = bK t * (bK u)⁻¹ := by
    exact mul_right_cancel (show
      (1 : ↥Conj.K) * (bK gamma)⁻¹ =
        (bK t * (bK u)⁻¹) * (bK gamma)⁻¹ by
      simpa only [one_mul] using hcancelLeft)
  apply bK_injective
  exact (mul_inv_eq_one.mp hcancelRight.symm)

end Omega
end Higman
end GroupApproximation
