import GroupApproximation.CharClass.ParityPHomog

/-!
# L4a, step six: the crux itself

`ParityPHomog.lean` proves the forward direction, that the substitution `X_a ↦ e_{a+1}`
carries weighted-homogeneous of weight `w` to homogeneous of degree `w`.  This file proves
the converse, which is the crux of L4a:

> the `e`-expansion of a symmetric polynomial homogeneous of degree `w` is
> weighted-homogeneous of weight `w`.

The argument is the only place in this lane that uses `esymmAlgEquiv`'s **surjectivity**
rather than its injectivity — through `eExpand`, which is its inverse — and it is the only
place a decomposition into components is taken.  Decompose the `e`-expansion into its
weighted-homogeneous components; each maps to something homogeneous of the corresponding
degree by the forward direction; uniqueness of the homogeneous decomposition of the image
kills every component but one; injectivity carries that back.

## Main results

* `GroupApproximation.CharClass.ParityP.esymmAeval_injective` — the substitution is
  injective.
* `ParityP.eExpand_isWeightedHomogeneous` — **the crux**.

Not here, and the next piece of work: the bridge `eCoeff a f = coeff (single a 1) (eExpand f)`,
which is what turns the crux into a statement about `eCoeff`.  It is a genuine missing
lemma, not bookkeeping — `eCoeff` is defined through the dual numbers and its equality with
the linear coefficient has to be checked on monomials.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section Converse

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The substitution `X_a ↦ e_{a+1}` is injective: it is `esymmAlgEquiv` followed by the
inclusion of the symmetric subalgebra. -/
theorem esymmAeval_injective :
    Function.Injective (fun G : MvPolynomial (Fin n) R =>
      aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1)) G) := by
  intro G H hGH
  refine (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).injective ?_
  refine Subtype.ext ?_
  simp only [esymmAlgEquiv_apply]
  rw [esymmAlgHom_apply, esymmAlgHom_apply]
  exact hGH

/-- A homogeneous polynomial has no component in any other degree.  Stated as a named
lemma because `IsHomogeneous` is a `def`, not a structure, so dot notation on a proof of it
resolves through the unfolded Pi type to `Function` and fails. -/
theorem homogeneousComponent_eq_zero_of_ne {m b : ℕ} {q : MvPolynomial (Fin n) R}
    (hq : MvPolynomial.IsHomogeneous q b) (hmb : m ≠ b) :
    homogeneousComponent m q = 0 := by
  rw [homogeneousComponent_of_mem hq, if_neg hmb]

/-- The image of a weighted-homogeneous component, as a homogeneous polynomial. -/
theorem isHomogeneous_aeval_component (m : ℕ) (F : MvPolynomial (Fin n) R) :
    MvPolynomial.IsHomogeneous
      (aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1))
        (weightedHomogeneousComponent (eWeight n) m F)) m :=
  isHomogeneous_esymmAeval (weightedHomogeneousComponent_isWeightedHomogeneous m F)

/-- **The crux of L4a.**  The `e`-expansion of a symmetric polynomial homogeneous of degree
`w` is weighted-homogeneous of weight `w`. -/
theorem eExpand_isWeightedHomogeneous {w : ℕ} (f : symmetricSubalgebra (Fin n) R)
    (hf : MvPolynomial.IsHomogeneous (f : MvPolynomial (Fin n) R) w) :
    MvPolynomial.IsWeightedHomogeneous (eWeight n) (eExpand f) w := by
  classical
  set F : MvPolynomial (Fin n) R := eExpand f with hFdef
  -- The `e`-expansion evaluates back to `f`.
  have hFval : aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1)) F
      = (f : MvPolynomial (Fin n) R) := by
    have h1 : esymmAlgHom (Fin n) R n (eExpand f) = f := by
      have h2 := (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).apply_symm_apply f
      rwa [esymmAlgEquiv_apply] at h2
    rw [hFdef, ← esymmAlgHom_apply, h1]
  -- The components form a finite family summing to `F`.
  have hfin : (Function.support fun m : ℕ =>
      weightedHomogeneousComponent (eWeight n) m F).Finite :=
    weightedHomogeneousComponent_finsupp F
  have hsum : ∑ m ∈ hfin.toFinset, weightedHomogeneousComponent (eWeight n) m F = F := by
    rw [← finsum_eq_sum _ hfin]
    exact sum_weightedHomogeneousComponent (eWeight n) F
  -- Every component of weight `≠ w` dies.
  have hkill : ∀ m : ℕ, m ≠ w → weightedHomogeneousComponent (eWeight n) m F = 0 := by
    intro m hm
    by_cases hmem : m ∈ hfin.toFinset
    · refine esymmAeval_injective ?_
      show aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1))
          (weightedHomogeneousComponent (eWeight n) m F)
        = aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1)) 0
      rw [map_zero]
      have hcomp : homogeneousComponent m (f : MvPolynomial (Fin n) R)
          = aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1))
              (weightedHomogeneousComponent (eWeight n) m F) := by
        conv_lhs => rw [← hFval, ← hsum]
        rw [map_sum, map_sum, Finset.sum_eq_single m]
        · exact homogeneousComponent_eq_self (isHomogeneous_aeval_component m F)
        · intro b _ hb
          exact homogeneousComponent_eq_zero_of_ne (isHomogeneous_aeval_component b F)
            (Ne.symm hb)
        · intro hnot
          exact absurd hmem hnot
      rw [← hcomp]
      exact homogeneousComponent_eq_zero_of_ne hf hm
    · simpa using hmem
  -- Hence every monomial of `F` has weight `w`.
  intro d hd
  by_contra hne
  have hzero := hkill (Finsupp.weight (eWeight n) d) hne
  have := coeff_weightedHomogeneousComponent (w := eWeight n)
    (Finsupp.weight (eWeight n) d) F d
  rw [hzero, coeff_zero, if_pos rfl] at this
  exact hd this.symm

end Converse

end ParityP

end GroupApproximation.CharClass
