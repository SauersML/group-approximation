import GroupApproximation.BooneHigman.Metabelian.ElemFPBhNagaoWireBase
import GroupApproximation.Meta.AxiomGuard

/-!
# LOUD: Nagao's theorem cannot shrink the OneVarNil conjunct of `P1`

Lane `bh-met-94c`, part 2 of 3.  The only instance of `PolyK2OneVarNilStatementOver (ZMod p)`
that concerns `F_p[X]` alone is `k = 0` (ring `F_p[∅][t]`).  Nagao covers it
(`bhNagaoWire_oneVarNilOver_zero`).  This module proves, with no hypothesis on `A`, that the
`k = 0` instance already follows from the `k = 1` instance (ring `A[s_0][t]`):
`A[∅][t]` is a retract of `A[s_0][t]` (by `C ∘ cc` and `C ∘ cc` on coefficients), compatibly
with `t ↦ 0`, and the conclusion is insensitive to one extra padding step.

Consequence (`bhNagaoWire_oneVarNilPos_iff`): OneVarNil restricted to `k ≥ 1` is logically
**equivalent** to OneVarNil.  So any "Nagao + finSuccEquiv" reduction of OneVarNil is an
equivalent restatement.  The multi-variable instances need homotopy invariance of `K₂` over
`F_p[s_1..s_k]` (Quillen); Nagao's one-variable theorem does not give them.  This module
therefore records the obstruction and states no new residual for OneVarNil.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Retract lemma**.  Let `ι : P₀ → P₁` have a left inverse `ρ` and let `ev₁ ∘ ι = c ∘ ev₀`.
If every `v ∈ K₂(N + 1, P₁)` with `ev₁ v = 1` dies after padding, then so does every
`u ∈ K₂(N, P₀)` with `ev₀ u = 1`. -/
theorem bhNagaoWire_nil_of_retract {P₀ P₁ Z₀ Z₁ : Type*} [Ring P₀] [Ring P₁] [Ring Z₀]
    [Ring Z₁] {N : ℕ} (ι : P₀ →+* P₁) (ρ : P₁ →+* P₀) (hρι : ρ.comp ι = RingHom.id P₀)
    (ev₀ : P₀ →+* Z₀) (ev₁ : P₁ →+* Z₁) (c : Z₀ →+* Z₁) (hev : ev₁.comp ι = c.comp ev₀)
    (h₁ : ∀ v : K2n (N + 1) P₁, K2Map ev₁ v = 1 →
      ∃ M : ℕ, ∃ hNM : N + 1 ≤ M, K2IndexMap (R := P₁) (Fin.castLEEmb hNM) v = 1)
    (u : K2n N P₀) (hu : K2Map ev₀ u = 1) :
    ∃ M : ℕ, ∃ hNM : N ≤ M, K2IndexMap (R := P₀) (Fin.castLEEmb hNM) u = 1 := by
  have hN1 : N ≤ N + 1 := Nat.le_succ N
  obtain ⟨M, hM, hMv⟩ := h₁ (K2Map ι (K2IndexMap (Fin.castLEEmb hN1) u)) (by
    rw [K2Map_K2Map, hev, ← K2Map_K2Map, ← K2IndexMap_K2Map, hu, map_one, map_one])
  refine ⟨M, hN1.trans hM, ?_⟩
  rw [← K2IndexMap_castLEEmb_castLEEmb hN1 hM u,
    ← K2Map_K2Map_of_comp_eq_id ρ ι hρι
      (K2IndexMap (Fin.castLEEmb hM) (K2IndexMap (Fin.castLEEmb hN1) u)),
    ← K2IndexMap_K2Map, hMv, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_nil_of_retract

/-- The inclusion `A[∅] → A[s_0]` (as `C ∘ cc`). -/
noncomputable def bhNagaoWire_up (A : Type*) [CommRing A] :
    MvPolynomial (Fin 0) A →+* MvPolynomial (Fin 1) A :=
  (MvPolynomial.C : A →+* MvPolynomial (Fin 1) A).comp
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 0) A →+* A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_up

/-- The retraction `A[s_0] → A[∅]`, `s_0 ↦ 0` (as `C ∘ cc`). -/
noncomputable def bhNagaoWire_down (A : Type*) [CommRing A] :
    MvPolynomial (Fin 1) A →+* MvPolynomial (Fin 0) A :=
  (MvPolynomial.C : A →+* MvPolynomial (Fin 0) A).comp
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) A →+* A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_down

/-- `down ∘ up = id` on `A[∅]`. -/
theorem bhNagaoWire_down_comp_up (A : Type*) [CommRing A] :
    (bhNagaoWire_down A).comp (bhNagaoWire_up A) = RingHom.id (MvPolynomial (Fin 0) A) := by
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := MvPolynomial.C_surjective (Fin 0) x
  simp only [bhNagaoWire_down, bhNagaoWire_up, RingHom.comp_apply, MvPolynomial.constantCoeff_C,
    RingHom.id_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_down_comp_up

/-- `down ∘ up = id` on coefficients, on `A[∅][t]`. -/
theorem bhNagaoWire_map_down_comp_up (A : Type*) [CommRing A] :
    (Polynomial.mapRingHom (bhNagaoWire_down A)).comp (Polynomial.mapRingHom (bhNagaoWire_up A)) =
      RingHom.id (Polynomial (MvPolynomial (Fin 0) A)) := by
  rw [Polynomial.mapRingHom_comp, bhNagaoWire_down_comp_up, Polynomial.mapRingHom_id]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_map_down_comp_up

/-- `t ↦ 0` commutes with `up` on coefficients. -/
theorem bhNagaoWire_eval_comp_map_up (A : Type*) [CommRing A] :
    (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin 1) A) →+* MvPolynomial (Fin 1) A).comp
        (Polynomial.mapRingHom (bhNagaoWire_up A)) =
      (bhNagaoWire_up A).comp (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin 0) A) →+* MvPolynomial (Fin 0) A) := by
  refine RingHom.ext fun q ↦ ?_
  simp only [RingHom.comp_apply]
  exact Polynomial.eval_zero_map (bhNagaoWire_up A) q

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_eval_comp_map_up

/-- **The `k = 0` instance of OneVarNil follows from the `k = 1` instance**, over any `A`.
Apply `bhNagaoWire_nil_of_retract` with `ι = map up`, `ρ = map down`, `c = up`. -/
theorem bhNagaoWire_oneVarNilZero_of_one (A : Type*) [CommRing A]
    (h₁ : ∀ N : ℕ, 1 + 5 ≤ N → ∀ v : K2n N (Polynomial (MvPolynomial (Fin 1) A)),
      K2Map (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin 1) A) →+* MvPolynomial (Fin 1) A) v = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := Polynomial (MvPolynomial (Fin 1) A)) (Fin.castLEEmb hNM) v = 1)
    (N : ℕ) (hN : 0 + 5 ≤ N) (u : K2n N (Polynomial (MvPolynomial (Fin 0) A)))
    (hu : K2Map (Polynomial.evalRingHom 0 :
        Polynomial (MvPolynomial (Fin 0) A) →+* MvPolynomial (Fin 0) A) u = 1) :
    ∃ M : ℕ, ∃ hNM : N ≤ M,
      K2IndexMap (R := Polynomial (MvPolynomial (Fin 0) A)) (Fin.castLEEmb hNM) u = 1 :=
  bhNagaoWire_nil_of_retract (Polynomial.mapRingHom (bhNagaoWire_up A))
    (Polynomial.mapRingHom (bhNagaoWire_down A)) (bhNagaoWire_map_down_comp_up A)
    (Polynomial.evalRingHom 0) (Polynomial.evalRingHom 0) (bhNagaoWire_up A)
    (bhNagaoWire_eval_comp_map_up A) (fun v hv ↦ h₁ (N + 1) (by omega) v hv) u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_oneVarNilZero_of_one

/-- `PolyK2OneVarNilStatementOver A` restricted to `k ≥ 1`.  LOUD: EQUIVALENT to
`PolyK2OneVarNilStatementOver A` (`bhNagaoWire_oneVarNilPos_iff`).  It is recorded only to
witness that the Nagao-covered instance `k = 0` carries no independent content; it is NOT
proposed as a residual. -/
def bhNagaoWire_OneVarNilPosStatementOver (A : Type*) [CommRing A] : Prop :=
  ∀ k N : ℕ, 0 < k → k + 5 ≤ N →
    ∀ u : K2n N (Polynomial (MvPolynomial (Fin k) A)),
      K2Map (Polynomial.evalRingHom 0 :
          Polynomial (MvPolynomial (Fin k) A) →+* MvPolynomial (Fin k) A) u = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := Polynomial (MvPolynomial (Fin k) A)) (Fin.castLEEmb hNM) u = 1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_OneVarNilPosStatementOver

/-- The `k ≥ 1` instances of OneVarNil give all of OneVarNil (the `k = 0` instance by
`bhNagaoWire_oneVarNilZero_of_one`). -/
theorem bhNagaoWire_oneVarNilOver_of_pos (A : Type*) [CommRing A]
    (h : bhNagaoWire_OneVarNilPosStatementOver A) : PolyK2OneVarNilStatementOver A := by
  intro k N hN u hu
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact bhNagaoWire_oneVarNilZero_of_one A (fun N' hN' v hv ↦ h 1 N' one_pos hN' v hv)
      N hN u hu
  · exact h k N hk hN u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_oneVarNilOver_of_pos

/-- **LOUD (strength)**: OneVarNil for `k ≥ 1` is equivalent to OneVarNil.  So removing the
Nagao-covered instance `k = 0` from the OneVarNil conjunct of `P1` changes nothing. -/
theorem bhNagaoWire_oneVarNilPos_iff (A : Type*) [CommRing A] :
    bhNagaoWire_OneVarNilPosStatementOver A ↔ PolyK2OneVarNilStatementOver A :=
  ⟨bhNagaoWire_oneVarNilOver_of_pos A, fun h k N _ hN u hu ↦ h k N hN u hu⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.bhNagaoWire_oneVarNilPos_iff

end GroupApproximation.BooneHigman.Metabelian.ElemFP
