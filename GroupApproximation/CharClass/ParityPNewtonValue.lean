import GroupApproximation.CharClass.ParityPNewton

/-!
# L4a, step three: Newton's identity modulo decomposables

Newton's identity, in the form Mathlib states it
(`MvPolynomial.psum_eq_mul_esymm_sub_sum`), reads

```text
  p_M  =  (−1)^{M+1} · M · e_M  −  ∑_{a + b = M, 0 < a < M} (−1)^a · e_a · p_b .
```

Every term of the subtracted sum is a product `e_a · p_b` with `a > 0` and `b = M − a > 0`,
so both factors have vanishing constant term and `eCoeff` kills the whole sum
(`ParityPSymmetric.eCoeff_mul_eq_zero`, whose hypotheses are exactly
`ParityPNewton.eLin_fst_esymm` and `eLin_fst_psum`).  What survives is

```text
  eCoeff j (p_M)  =  (−1)^{M+1} · M · eCoeff j (e_M) ,
```

which is "`p_M ≡ (−1)^{M−1} M e_M` modulo decomposables" with no quotient ring anywhere.
This is the step `sp-design`'s L4a proof calls "Newton on the indecomposables", and it is
the only place Newton is used.

The bookkeeping cost is the lift from `MvPolynomial (Fin n) R`, where Mathlib states the
identity, to `symmetricSubalgebra (Fin n) R`, where `eCoeff` lives.  It is done once, by
`Subtype.ext`, with the scalars carried as `R`-smuls so that `eCoeff`'s linearity applies
directly.

## Main results

* `GroupApproximation.CharClass.ParityP.psumSub` — `p_M` in the symmetric subalgebra.
* `ParityP.psumSub_eq_newton` — Newton's identity, lifted.
* `ParityP.eCoeff_psumSub` — `eCoeff j (p_M) = (−1)^{M+1} · M · eCoeff j (e_M)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section NewtonValue

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `p_M`, as an element of the symmetric subalgebra. -/
noncomputable def psumSub (R : Type*) [CommRing R] (n M : ℕ) :
    symmetricSubalgebra (Fin n) R :=
  ⟨psum (Fin n) R M, psum_isSymmetric (Fin n) R M⟩

@[simp] theorem psumSub_coe (M : ℕ) :
    ((psumSub R n M : symmetricSubalgebra (Fin n) R) : MvPolynomial (Fin n) R)
      = psum (Fin n) R M := rfl

@[simp] theorem esymmSub_coe (a : ℕ) :
    ((esymmSub R n a : symmetricSubalgebra (Fin n) R) : MvPolynomial (Fin n) R)
      = esymm (Fin n) R a := rfl

/-! ### `eCoeff` is `R`-linear -/

theorem eCoeff_smul (j : Fin n) (c : R) (f : symmetricSubalgebra (Fin n) R) :
    eCoeff j (c • f) = c * eCoeff j f := by
  rw [eCoeff, eCoeff, ← eLinHom_apply, ← eLinHom_apply, map_smul, TrivSqZeroExt.snd_smul,
    smul_eq_mul]

/-! ### Newton's identity in the subalgebra -/

/-- The index set of the subtracted sum in Newton's identity. -/
noncomputable def newtonIdx (M : ℕ) : Finset (ℕ × ℕ) :=
  {a ∈ Finset.antidiagonal M | a.1 ∈ Set.Ioo 0 M}

theorem newtonIdx_mem {M : ℕ} {a : ℕ × ℕ} (ha : a ∈ newtonIdx M) :
    0 < a.1 ∧ 0 < a.2 := by
  rw [newtonIdx, Finset.mem_filter, Finset.mem_antidiagonal] at ha
  obtain ⟨hsum, h1, h2⟩ := ha
  exact ⟨h1, by omega⟩

/-- **Newton's identity, lifted to the symmetric subalgebra**, with the scalars carried as
`R`-smuls so that `eCoeff`'s linearity applies directly. -/
theorem psumSub_eq_newton (M : ℕ) (hM : 0 < M) :
    psumSub R n M
      = (((-1 : R) ^ (M + 1) * (M : R)) • esymmSub R n M)
        - ∑ a ∈ newtonIdx M,
            ((-1 : R) ^ a.1) • (esymmSub R n a.1 * psumSub R n a.2) := by
  apply Subtype.ext
  push_cast
  rw [psumSub_coe]
  have hN := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) R M hM
  rw [hN, newtonIdx]
  congr 1
  · rw [MvPolynomial.smul_eq_C_mul, esymmSub_coe]
    simp only [map_neg, map_mul, map_pow, map_natCast, map_one]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, esymmSub_coe, psumSub_coe]
    simp only [map_neg, map_pow, map_one]
    ring

/-! ### The value -/

/-- **Newton modulo decomposables.**  `eCoeff j (p_M) = (−1)^{M+1} · M · eCoeff j (e_M)`:
every term of the subtracted sum in Newton's identity is a product of two symmetric
polynomials of positive index, hence has vanishing constant term in both factors, hence is
killed by `eCoeff`. -/
theorem eCoeff_psumSub (j : Fin n) (M : ℕ) (hM : 0 < M) :
    eCoeff j (psumSub R n M)
      = (-1 : R) ^ (M + 1) * (M : R) * eCoeff j (esymmSub R n M) := by
  rw [psumSub_eq_newton M hM, eCoeff_sub, eCoeff_smul, eCoeff_sum]
  have hzero : ∀ a ∈ newtonIdx M,
      eCoeff j (((-1 : R) ^ a.1) • (esymmSub R n a.1 * psumSub R n a.2)) = 0 := by
    intro a ha
    obtain ⟨h1, h2⟩ := newtonIdx_mem ha
    have hz : eCoeff j (esymmSub R n a.1 * psumSub R n a.2) = 0 :=
      eCoeff_mul_eq_zero j _ _ (eLin_fst_esymm j h1) (eLin_fst_psum j h2)
    rw [eCoeff_smul, hz, mul_zero]
  rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, sub_zero]

end NewtonValue

end ParityP

end GroupApproximation.CharClass
