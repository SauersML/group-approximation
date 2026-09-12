import GroupApproximation.CharClass.ParityPCoeffBridge

/-!
# The twist on the symmetric subalgebra

Lane `lix-evenside` (successor of `sp-evenside`), L4a of `sp-design` §3.3.

`ParityPTwist.lean` defines the substitution `φ_κ : y ↦ y + κ·y^p` as an algebra endomorphism
of `R[X_0,…,X_{n-1}]`.  The functional `eCoeff` lives on the symmetric subalgebra, so the
assembly of L4a needs `φ_κ` restricted there, together with the one fact about constant terms
that lets `eCoeff_mul_eq_zero` fire on twisted products.

## Main results

* `ParityP.rename_twist` — `φ_κ` commutes with every permutation of the variables.
* `ParityP.twist_isSymmetric` — hence `φ_κ` preserves symmetric polynomials.
* `ParityP.twistSub` — `φ_κ` as an algebra endomorphism of `symmetricSubalgebra (Fin n) R`.
* `ParityP.aeval_zero_twist`, `ParityP.eLin_twistSub_fst` — `φ_κ` does not move the constant
  term, for `p ≥ 1`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section TwistSymm

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The twist commutes with renaming the variables by a permutation: both send `X k` to
`X (e k) + C κ * X (e k) ^ p`. -/
theorem rename_twist (p : ℕ) (κ : R) (e : Equiv.Perm (Fin n)) (f : MvPolynomial (Fin n) R) :
    rename e (twist R n p κ f) = twist R n p κ (rename e f) := by
  have h : (rename (e : Fin n → Fin n)).comp (twist R n p κ)
      = (twist R n p κ).comp (rename (e : Fin n → Fin n)) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [AlgHom.comp_apply, twist_X, rename_X, map_add, map_mul, map_pow, rename_C]
  exact congrArg (fun g => g f) h

/-- **The twist preserves symmetric polynomials.** -/
theorem twist_isSymmetric (p : ℕ) (κ : R) {f : MvPolynomial (Fin n) R} (hf : f.IsSymmetric) :
    (twist R n p κ f).IsSymmetric := by
  intro e
  rw [rename_twist, hf e]

/-- The twist, as an algebra endomorphism of the symmetric subalgebra. -/
noncomputable def twistSub (p : ℕ) (κ : R) :
    symmetricSubalgebra (Fin n) R →ₐ[R] symmetricSubalgebra (Fin n) R :=
  ((twist R n p κ).comp (symmetricSubalgebra (Fin n) R).val).codRestrict
    (symmetricSubalgebra (Fin n) R) fun f =>
      (mem_symmetricSubalgebra _).mpr
        (twist_isSymmetric p κ ((mem_symmetricSubalgebra _).mp f.2))

theorem twistSub_coe (p : ℕ) (κ : R) (f : symmetricSubalgebra (Fin n) R) :
    ((twistSub p κ f : symmetricSubalgebra (Fin n) R) : MvPolynomial (Fin n) R)
      = twist R n p κ (f : MvPolynomial (Fin n) R) := rfl

/-- The twist does not move the constant term: every variable goes to `X k + κ·X k ^ p`,
which vanishes at `0` once `p ≥ 1`. -/
theorem aeval_zero_twist {p : ℕ} (hp : 1 ≤ p) (κ : R) (f : MvPolynomial (Fin n) R) :
    aeval (fun _ : Fin n => (0 : R)) (twist R n p κ f)
      = aeval (fun _ : Fin n => (0 : R)) f := by
  have h : (aeval (fun _ : Fin n => (0 : R))).comp (twist R n p κ)
      = aeval (fun _ : Fin n => (0 : R)) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    have hp0 : p ≠ 0 := by omega
    simp [twist_X, zero_pow hp0]
  exact congrArg (fun g => g f) h

/-- The `fst` of `eLin` is unchanged by the twist, so a factor with vanishing constant term
keeps it after twisting. -/
theorem eLin_twistSub_fst {p : ℕ} (hp : 1 ≤ p) (κ : R) (j : Fin n)
    (f : symmetricSubalgebra (Fin n) R) :
    (eLin j (twistSub p κ f)).fst = (eLin j f).fst := by
  rw [eLin_fst, eLin_fst, twistSub_coe, aeval_zero_twist hp]

end TwistSymm

end ParityP

end GroupApproximation.CharClass
