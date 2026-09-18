import GroupApproximation.BooneHigman.Metabelian.ElemFPK2Stability
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The nil part of `K₂(N, F_p[s_1..s_k])`: reduction to one variable

Lane `bh-met-22`.  Lane `bh-met-14` (module `ElemFPK2Homotopy`) isolated `PolyK2NilPosStatement`:
for `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element `u ∈ K₂(N, F_p[s_1..s_k])` killed by setting all
variables to `0` dies after padding.  This module removes the induction on the number of
variables.

* `PolyK2OneVarNilStatement`: for `A = F_p[s_1..s_k]` and `N ≥ k + 5`, an element
  `u ∈ K₂(N, A[t])` killed by `t ↦ 0` dies after padding.  **This is the isolated gap.**
* `nil_of_factor`: the inductive step, for arbitrary rings.  Let `ψ : B ≅ A[t]`, and let the
  evaluation `cc_B : B → Z` factor as `cc_A ∘ ev_{t=0} ∘ ψ`.  Put `u' = ψ u`, `w = ev u'`.  Then
  `u' = (u' · (C w)⁻¹) · C w`.  The first factor is killed by `ev` (because `ev ∘ C = id`), so it
  dies by the one-variable statement.  `w` is killed by `cc_A`, so it dies by the induction
  hypothesis, and then so does `C w` (naturality `K2IndexMap_K2Map`).  Padding both to the
  maximum of the two ranks kills `u'`, and `ψ⁻¹` carries this back to `u`.
* `polyK2Nil_of_oneVar`: induction on `k` through `MvPolynomial.finSuccEquiv`,
  `F_p[s_0..s_k] ≅ F_p[s_1..s_k][s_0]`.  The case `k = 0` is `eq_one_of_K2Map_constantCoeff_eq_one`.
  At `k + 1` the hypothesis `N ≥ k + 5` feeds the one-variable statement and `N ≥ k + 4` the
  induction hypothesis.
* `polyK2NilPos_of_oneVar`, `polynomialFpK2Vanishing_of_oneVar`: the endpoints.
* `polyK2OneVarNil_of_nilPos`: the converse.  So the gap is not logically stronger than
  `PolyK2NilPosStatement`; what it removes is the induction and the splitting.

Truth of the gap.  `A = F_p[s_1..s_k]` is regular noetherian, so Quillen's homotopy invariance gives
`K₂(A[t]) = K₂(A)` stably, i.e. the kernel `NK₂(A)` of `ev_{t=0}` on stable `K₂(A[t])` is `0`.
Stable `K₂(R) = ker(St(R) → E(R))` is the filtered colimit of the unstable `K₂(n, R)`, so an
unstable element whose stable image is `0` dies at some finite rank.  No rank bound is needed, so
`N ≥ k + 5` (the bound `(k + 1) + 4` that the induction passes on) is harmless.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The isolated gap**: the nil part of homotopy invariance in one variable over
`A = F_p[s_1..s_k]`, for `N ≥ k + 5`.  An element of `K₂(N, A[t])` killed by `t ↦ 0` dies after
padding. -/
def PolyK2OneVarNilStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 5 ≤ N →
    ∀ u : K2n N (Polynomial (MvPolynomial (Fin k) (ZMod p))),
      K2Map (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) (ZMod p)) →+* MvPolynomial (Fin k) (ZMod p)) u = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := Polynomial (MvPolynomial (Fin k) (ZMod p))) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2OneVarNilStatement

/-- **The inductive step**, for arbitrary rings.  If `cc_B = cc_A ∘ ev ∘ ψ` with `ψ` invertible and
`ev ∘ C = id`, then the nil parts for `ev` and for `cc_A` give the nil part for `cc_B`. -/
theorem nil_of_factor {A B P Z : Type*} [Ring A] [Ring B] [Ring P] [Ring Z] {N : ℕ}
    (ψ : B →+* P) (ψinv : P →+* B) (hψ : ψinv.comp ψ = RingHom.id B)
    (ev : P →+* A) (C : A →+* P) (hev : ev.comp C = RingHom.id A)
    (ccA : A →+* Z) (ccB : B →+* Z) (hcc : (ccA.comp ev).comp ψ = ccB)
    (hone : ∀ v : K2n N P, K2Map ev v = 1 →
      ∃ M : ℕ, ∃ hNM : N ≤ M, K2IndexMap (R := P) (Fin.castLEEmb hNM) v = 1)
    (hih : ∀ w : K2n N A, K2Map ccA w = 1 →
      ∃ M : ℕ, ∃ hNM : N ≤ M, K2IndexMap (R := A) (Fin.castLEEmb hNM) w = 1)
    (u : K2n N B) (hu : K2Map ccB u = 1) :
    ∃ M : ℕ, ∃ hNM : N ≤ M, K2IndexMap (R := B) (Fin.castLEEmb hNM) u = 1 := by
  obtain ⟨M₂, h₂, hM₂⟩ := hih (K2Map ev (K2Map ψ u))
    (by rw [K2Map_K2Map, K2Map_K2Map, hcc, hu])
  obtain ⟨M₁, h₁, hM₁⟩ := hone (K2Map ψ u * (K2Map C (K2Map ev (K2Map ψ u)))⁻¹)
    (by rw [map_mul, map_inv, K2Map_K2Map_of_comp_eq_id ev C hev, mul_inv_cancel])
  have hN : N ≤ max M₁ M₂ := h₁.trans (le_max_left M₁ M₂)
  refine ⟨max M₁ M₂, hN, ?_⟩
  have hv := K2IndexMap_eq_one_of_le h₁ (le_max_left M₁ M₂) hN hM₁
  have hw := K2IndexMap_eq_one_of_le h₂ (le_max_right M₁ M₂) hN hM₂
  have hsplit : K2Map ψ u =
      K2Map ψ u * (K2Map C (K2Map ev (K2Map ψ u)))⁻¹ * K2Map C (K2Map ev (K2Map ψ u)) :=
    (inv_mul_cancel_right _ _).symm
  have hpad : K2IndexMap (Fin.castLEEmb hN) (K2Map ψ u) = 1 := by
    rw [hsplit, map_mul, hv, one_mul, K2IndexMap_K2Map, hw, map_one]
  rw [← K2Map_K2Map_of_comp_eq_id ψinv ψ hψ u, K2IndexMap_K2Map, hpad, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.nil_of_factor

/-- **The induction on the number of variables**: the one-variable nil part gives the nil part
for every `k`. -/
theorem polyK2Nil_of_oneVar (h : PolyK2OneVarNilStatement) : PolyK2NilStatement := by
  intro p hp k
  induction k with
  | zero =>
    intro N _ _ u hu
    exact ⟨N, le_rfl, by rw [eq_one_of_K2Map_constantCoeff_eq_one hu, map_one]⟩
  | succ k ih =>
    intro N hkN h5N u hu
    exact nil_of_factor (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.symm.toRingHom
      (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.symm_toRingHom_comp_toRingHom
      (Polynomial.evalRingHom 0) Polynomial.C evalRingHom_zero_comp_C
      MvPolynomial.constantCoeff MvPolynomial.constantCoeff (constantCoeff_comp_finSuccEquiv k)
      (h p hp k N (by omega)) (ih N (by omega) h5N) u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2Nil_of_oneVar

/-- **Endpoint**: the one-variable nil part gives the isolated gap `PolyK2NilPosStatement` of
lane `bh-met-14`. -/
theorem polyK2NilPos_of_oneVar (h : PolyK2OneVarNilStatement) : PolyK2NilPosStatement :=
  fun p hp k N _ hkN h5N ↦ polyK2Nil_of_oneVar h p hp k N hkN h5N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilPos_of_oneVar

/-- Conversely, `PolyK2NilPosStatement` gives the one-variable nil part, so the gap is not
logically stronger than it. -/
theorem polyK2OneVarNil_of_nilPos (h : PolyK2NilPosStatement) : PolyK2OneVarNilStatement := by
  intro p hp k N hkN u hu
  obtain ⟨M, hNM, hM⟩ := h p hp (k + 1) N (Nat.succ_pos k) (by omega) (by omega)
    (K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.symm.toRingHom u)
    (by
      rw [← constantCoeff_comp_finSuccEquiv (R := ZMod p) k, ← K2Map_K2Map, ← K2Map_K2Map,
        K2Map_K2Map_of_comp_eq_id _ _
          (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom_comp_symm_toRingHom,
        hu, map_one])
  refine ⟨M, hNM, ?_⟩
  rw [← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom_comp_symm_toRingHom u,
    K2IndexMap_K2Map, hM, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2OneVarNil_of_nilPos

/-- **Combined endpoint**: the stability gap, the one-variable nil gap and the field case give
`K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_oneVar (hstab : PolyK2NilStabilityPosStatement)
    (hone : PolyK2OneVarNilStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_nilPos hstab (polyK2NilPos_of_oneVar hone) hfield

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_oneVar

end GroupApproximation.BooneHigman.Metabelian.ElemFP
