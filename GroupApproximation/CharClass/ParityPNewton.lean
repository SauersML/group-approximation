import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import GroupApproximation.CharClass.ParityPSymmetric

/-!
# L4a, step two: the coefficient functional is linear and kills constant-term-free products

`ParityPSymmetric.lean` defines the `e`-expansion and the coefficient functional `eCoeff`,
and shows it is `1` on the elementary symmetric polynomial it names and that it kills a
product of two elements whose `eLin`-image has vanishing `fst`.  This file supplies the two
things that turn those into a usable calculus:

* `eLin` is an **algebra homomorphism** `Λ_{Fin n} →ₐ[R] R[ε]` — it is one by construction,
  being `aeval` after the inverse of `esymmAlgEquiv`, but `ParityPSymmetric.lean` states it
  as a plain function, so the bundled form is introduced here and shown to agree by `rfl`.
* The `fst` of `eLin` is **evaluation at zero of the symmetric polynomial itself**, not of
  its `e`-expansion.  That is what makes the hypothesis of `eCoeff_mul_eq_zero` checkable:
  a symmetric polynomial with vanishing constant term has vanishing `fst`, and both `esymm`
  and `psum` of positive index have vanishing constant term.

The proof of the second is one application of `MvPolynomial.algHom_ext`: `aeval 0` and
`aeval 0 ∘ esymmAlgHom` are two algebra maps `R[X_0,…,X_{n-1}] → R` that agree on the
variables, because `e_{i+1}` has no constant term.  No `constantCoeff` bookkeeping and no
grading.

## Main results

* `GroupApproximation.CharClass.ParityP.eLinHom` — `eLin`, bundled.
* `ParityP.constantCoeff_esymm` — `e_a` has no constant term for `a ≥ 1`.
* `ParityP.eLin_fst` — the `fst` of `eLin` is `aeval 0` of the symmetric polynomial.
* `ParityP.eLin_fst_esymm`, `ParityP.eLin_fst_psum` — it vanishes on `e_a` and `p_a` for
  `a ≥ 1`.
* `ParityP.eCoeff_add`, `eCoeff_zero`, `eCoeff_neg`, `eCoeff_sub`, `eCoeff_sum` — the
  calculus.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section Newton

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `eLin`, as an algebra homomorphism.  It is one by construction. -/
noncomputable def eLinHom (j : Fin n) :
    symmetricSubalgebra (Fin n) R →ₐ[R] DualNumber R :=
  (aeval (fun k => if k = j then (DualNumber.eps : DualNumber R) else 0)).comp
    (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).symm.toAlgHom

theorem eLinHom_apply (j : Fin n) (f : symmetricSubalgebra (Fin n) R) :
    eLinHom j f = eLin j f := rfl

/-! ### The `fst` of `eLin` is evaluation at zero -/

/-- An elementary symmetric polynomial of positive index has vanishing constant term. -/
theorem constantCoeff_esymm {a : ℕ} (ha : 1 ≤ a) :
    constantCoeff (esymm (Fin n) R a) = 0 := by
  rw [esymm, map_sum]
  refine Finset.sum_eq_zero fun B hB => ?_
  have hcard : B.card = a := (Finset.mem_powersetCard.mp hB).2
  obtain ⟨k, hk⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
  rw [map_prod]
  exact Finset.prod_eq_zero hk (by simp)

/-- Evaluating the `e`-expansion at zero is the same as evaluating the symmetric polynomial
itself at zero: the two algebra maps agree on the variables, because `e_{i+1}` has no
constant term. -/
theorem aeval_zero_eExpand (f : symmetricSubalgebra (Fin n) R) :
    aeval (fun _ : Fin n => (0 : R)) (eExpand f)
      = aeval (fun _ : Fin n => (0 : R)) (f : MvPolynomial (Fin n) R) := by
  have hext : (aeval (fun _ : Fin n => (0 : R))).comp
      ((symmetricSubalgebra (Fin n) R).val.comp
        (esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).toAlgHom)
      = aeval (fun _ : Fin n => (0 : R)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, esymmAlgEquiv_apply,
      Subalgebra.coe_val, aeval_X]
    rw [esymmAlgHom_apply]
    have hc : constantCoeff (esymm (Fin n) R ((i : ℕ) + 1)) = 0 :=
      constantCoeff_esymm (by omega)
    simp [hc]
  have h := congrArg (fun g => g (eExpand f)) hext
  simpa [eExpand] using h.symm

/-- The `fst` of `eLin` is evaluation of the symmetric polynomial at zero. -/
theorem eLin_fst (j : Fin n) (f : symmetricSubalgebra (Fin n) R) :
    (eLin j f).fst = aeval (fun _ : Fin n => (0 : R)) (f : MvPolynomial (Fin n) R) := by
  have hext : (TrivSqZeroExt.fstHom R R R).comp
      (aeval (fun k : Fin n => if k = j then (DualNumber.eps : DualNumber R) else 0))
      = aeval (fun _ : Fin n => (0 : R)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
    by_cases h : i = j
    · rw [if_pos h]
      show (DualNumber.eps : DualNumber R).fst = 0
      rw [DualNumber.eps, TrivSqZeroExt.fst_inr]
    · rw [if_neg h, map_zero]
  have h1 : (eLin j f).fst = aeval (fun _ : Fin n => (0 : R)) (eExpand f) :=
    congrArg (fun g => g (eExpand f)) hext
  rw [h1]
  exact aeval_zero_eExpand f

/-- `e_a` has vanishing constant term for `a ≥ 1`. -/
theorem eLin_fst_esymm (j : Fin n) {a : ℕ} (ha : 1 ≤ a) :
    (eLin j (esymmSub R n a)).fst = 0 := by
  rw [eLin_fst]
  show aeval (fun _ : Fin n => (0 : R)) (esymm (Fin n) R a) = 0
  rw [esymm, map_sum]
  refine Finset.sum_eq_zero fun B hB => ?_
  have hcard : B.card = a := (Finset.mem_powersetCard.mp hB).2
  have hne : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k, hk⟩ := hne
  rw [map_prod]
  refine Finset.prod_eq_zero hk ?_
  simp

/-- `p_a` has vanishing constant term for `a ≥ 1`. -/
theorem eLin_fst_psum (j : Fin n) {a : ℕ} (ha : 1 ≤ a) :
    (eLin j ⟨psum (Fin n) R a, psum_isSymmetric (Fin n) R a⟩).fst = 0 := by
  rw [eLin_fst]
  show aeval (fun _ : Fin n => (0 : R)) (psum (Fin n) R a) = 0
  rw [psum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_pow, aeval_X]
  exact zero_pow (by omega)

/-! ### The calculus of `eCoeff` -/

theorem eCoeff_add (j : Fin n) (f g : symmetricSubalgebra (Fin n) R) :
    eCoeff j (f + g) = eCoeff j f + eCoeff j g := by
  rw [eCoeff, eCoeff, eCoeff, ← eLinHom_apply, ← eLinHom_apply, ← eLinHom_apply, map_add,
    TrivSqZeroExt.snd_add]

theorem eCoeff_zero (j : Fin n) : eCoeff j (0 : symmetricSubalgebra (Fin n) R) = 0 := by
  rw [eCoeff, ← eLinHom_apply, map_zero, TrivSqZeroExt.snd_zero]

theorem eCoeff_neg (j : Fin n) (f : symmetricSubalgebra (Fin n) R) :
    eCoeff j (-f) = -eCoeff j f := by
  rw [eCoeff, eCoeff, ← eLinHom_apply, ← eLinHom_apply, map_neg, TrivSqZeroExt.snd_neg]

theorem eCoeff_sub (j : Fin n) (f g : symmetricSubalgebra (Fin n) R) :
    eCoeff j (f - g) = eCoeff j f - eCoeff j g := by
  rw [sub_eq_add_neg, eCoeff_add, eCoeff_neg, ← sub_eq_add_neg]

theorem eCoeff_sum (j : Fin n) {ι' : Type*} (f : ι' → symmetricSubalgebra (Fin n) R) :
    ∀ s : Finset ι', eCoeff j (∑ i ∈ s, f i) = ∑ i ∈ s, eCoeff j (f i) := by
  intro s
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, eCoeff_zero]
  | cons a v _ha ihv => rw [Finset.sum_cons, Finset.sum_cons, eCoeff_add, ihv]

end Newton

end ParityP

end GroupApproximation.CharClass
