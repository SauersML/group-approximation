import Mathlib.Algebra.MvPolynomial.Rename
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVar
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabRange
import GroupApproximation.Meta.AxiomGuard

/-!
# The nil part of `K₂(N, A[t_0..t_{k-1}])` over an arbitrary base ring: statements and reductions

Lane `bh-met-37`, generic module.  The char-`p` lanes `bh-met-22` (`ElemFPK2OneVar`) and
`bh-met-29` (`ElemFPK2StabRange`) proved two reductions for the base ring `F_p`.  Their proofs use
nothing about `F_p`: the inductive step `nil_of_factor` and the retraction lemma
`eq_one_of_K2Stab_retract` are already stated for arbitrary rings.  This module restates the gaps
for an arbitrary commutative base ring `A`, and reproves the two reductions over `A`.

* `PolyK2OneVarNilStatementOver A`: for `N ≥ k + 5`, an element of `K₂(N, A[s_1..s_k][t])` killed
  by `t ↦ 0` dies after padding.
* `PolyK2NilStatementOver A`: for `N ≥ k + 4`, `N ≥ 5`, an element of `K₂(N, A[s_1..s_k])` killed
  by `ev₀` dies after padding.
* `polyK2NilOver_of_oneVar`: the first gives the second, by induction on `k` through
  `MvPolynomial.finSuccEquiv` (the proof of `ElemFP.polyK2Nil_of_oneVar`, with `ZMod p` replaced
  by `A`).
* `PolyK2StabRangeDiagStatementOver A d`: for `k ≥ 1`, an element `u ∈ K₂(k + d, A[s_1..s_k])`
  with `ev₀ u = 1` and `K2Stab u = 1` is trivial.  The rank offset `d` is a parameter so that the
  safer offset `d = 5` can be used instead of `d = 4` (see the truth check in
  `ElemFPCharZeroK2NilEndpoint`).
* `PolyK2NilStabilityStatementOver A d`: the same for every rank `N ≥ k + d`.
* `polyK2NilStabilityOver_of_diag`: the diagonal case gives every rank, by adding dummy variables
  (the proof of `ElemFP.polyK2NilStabilityPos_of_diag`, with `4` replaced by `d`).

No hypothesis on `A` is needed for the reductions.  Whether the statements hold depends on `A`.
They hold for regular noetherian `A` of finite Krull dimension (see the endpoint modules).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section Statements

variable (A : Type*) [CommRing A]

/-- **One-variable nil part over `A`.**  For `N ≥ k + 5`, an element of `K₂(N, A[s_1..s_k][t])`
killed by `t ↦ 0` dies after padding. -/
def PolyK2OneVarNilStatementOver : Prop :=
  ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (Polynomial (MvPolynomial (Fin k) A)),
      K2Map (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) A) →+* MvPolynomial (Fin k) A) u = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := Polynomial (MvPolynomial (Fin k) A)) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2OneVarNilStatementOver

/-- **Nil part over `A`**, all `k`.  For `N ≥ k + 4`, `N ≥ 5`, an element of `K₂(N, A[s_1..s_k])`
killed by `ev₀` dies after padding. -/
def PolyK2NilStatementOver : Prop :=
  ∀ k N : ℕ, k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A) u = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := MvPolynomial (Fin k) A) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilStatementOver

/-- **Diagonal injective stability on `ker ev₀` over `A`**, at rank `k + d`, `k ≥ 1`. -/
def PolyK2StabRangeDiagStatementOver (d : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ u : K2n (k + d) (MvPolynomial (Fin k) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A) u = 1 →
        K2Stab (k + d) (MvPolynomial (Fin k) A) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2StabRangeDiagStatementOver

/-- **Injective stability on `ker ev₀` over `A`** at every rank `N ≥ k + d`, `k ≥ 1`. -/
def PolyK2NilStabilityStatementOver (d : ℕ) : Prop :=
  ∀ k N : ℕ, 0 < k → k + d ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A) u = 1 →
        K2Stab N (MvPolynomial (Fin k) A) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilStabilityStatementOver

/-- **The ring-generic gap pair** at offset `d`: the one-variable nil part and diagonal injective
stability on `ker ev₀`. -/
def PolyK2NilGapStatementOver (d : ℕ) : Prop :=
  PolyK2OneVarNilStatementOver A ∧ PolyK2StabRangeDiagStatementOver A d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilGapStatementOver

/-- **Vanishing of the nil part over `A`** at ranks `N ≥ k + d`, `k ≥ 1`: an element of
`K₂(N, A[s_1..s_k])` killed by `ev₀` is trivial. -/
def PolyK2NilPosStatementOver (d : ℕ) : Prop :=
  ∀ k N : ℕ, 0 < k → k + d ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) A),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilPosStatementOver

end Statements

/-- **Induction on the number of variables over `A`**: the one-variable nil part gives the nil
part for every `k`. -/
theorem polyK2NilOver_of_oneVar (A : Type*) [CommRing A] (h : PolyK2OneVarNilStatementOver A) :
    PolyK2NilStatementOver A := by
  intro k
  induction k with
  | zero =>
    intro N _ _ u hu
    exact ⟨N, le_rfl, by rw [eq_one_of_K2Map_constantCoeff_eq_one hu, map_one]⟩
  | succ k ih =>
    intro N hkN h5N u hu
    exact nil_of_factor (MvPolynomial.finSuccEquiv A k).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv A k).toRingEquiv.symm.toRingHom
      (MvPolynomial.finSuccEquiv A k).toRingEquiv.symm_toRingHom_comp_toRingHom
      (Polynomial.evalRingHom 0) Polynomial.C evalRingHom_zero_comp_C
      MvPolynomial.constantCoeff MvPolynomial.constantCoeff (constantCoeff_comp_finSuccEquiv k)
      (h k N (by omega)) (ih N (by omega) h5N) u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilOver_of_oneVar

/-- **Rank reduction over `A`**: the diagonal case `N = k + d` gives injective stability on
`ker ev₀` at every rank `N ≥ k + d`, by adding `N - d - k` dummy variables. -/
theorem polyK2NilStabilityOver_of_diag (A : Type*) [CommRing A] (d : ℕ)
    (h : PolyK2StabRangeDiagStatementOver A d) : PolyK2NilStabilityStatementOver A d := by
  intro k N hk hkN u hu0 hu
  obtain ⟨k', rfl⟩ : ∃ k' : ℕ, N = k' + d := ⟨N - d, by omega⟩
  have hkk : k ≤ k' := by omega
  exact eq_one_of_K2Stab_retract
    (MvPolynomial.rename (R := A) (Fin.castLE hkk)).toRingHom
    (MvPolynomial.killCompl (R := A) (Fin.castLE_injective hkk)).toRingHom
    (RingHom.ext fun x ↦ MvPolynomial.killCompl_rename_app (Fin.castLE_injective hkk) x)
    (MvPolynomial.constantCoeff : MvPolynomial (Fin k) A →+* A)
    (MvPolynomial.constantCoeff : MvPolynomial (Fin k') A →+* A)
    (RingHom.ext fun x ↦ MvPolynomial.constantCoeff_rename (Fin.castLE hkk) x)
    (h k' (hk.trans_le hkk)) u hu0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilStabilityOver_of_diag

end GroupApproximation.BooneHigman.Metabelian.ElemFP
