import GroupApproximation.BooneHigman.Metabelian.ElemFPK2Split
import GroupApproximation.Meta.AxiomGuard

/-!
# Homotopy invariance for `K₂(N, F_p[s_1..s_k])`: the retraction and the nil part

Lane `bh-met-14`.  `PolyK2HomotopyStatement` (module `ElemFPK2Split`) says that every element of
`K₂(N, R_k)`, `R_k = F_p[s_1..s_k]`, becomes a constant after padding.  This module proves its
formal part for any commutative ring `R` and any variable type `σ`.  The evaluation at `0`,
`constantCoeff : R[σ] → R`, retracts `C : R → R[σ]`.  So:

* `K2Map_constantCoeff_K2Map_C`: `ev₀ ∘ C = id` on `K₂(I, R)`;
* `K2Map_C_injective`: `K₂(I, R) → K₂(I, R[σ])` is injective (the "injective half");
* `K2Map_constantCoeff_split`: `u = C(ev₀ u) · w` with `ev₀ w = 1`;
* `eq_one_of_K2Map_constantCoeff_eq_one`: with no variables (`IsEmpty σ`), `ev₀` is injective.

The remaining content of homotopy invariance is the *nil part*: an element killed by `ev₀` dies
after padding.

* `PolyK2NilStatement`: the nil part for all `k`.  It is equivalent to `PolyK2HomotopyStatement`,
  in both directions with proofs: `polyK2Homotopy_of_nil` (by the splitting) and
  `polyK2Nil_of_homotopy`.
* `PolyK2NilPosStatement`: the nil part for `k ≥ 1` only.  **This is the isolated gap.**  It is
  strictly smaller than `PolyK2HomotopyStatement`: the splitting, the retraction and the
  case `k = 0` (where `ev₀` is an isomorphism) are proved here (`polyK2Nil_of_pos`).  It is true:
  it follows from homotopy invariance (`polyK2Nil_of_homotopy`), which is true by Quillen's
  theorem `K₂(A[t]) = K₂(A)` for regular `A`, applied `k` times, plus the filtered-colimit
  description of stable `K₂`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section Retraction

variable {σ R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- `ev₀ ∘ C = id` on `K₂(I, R)`. -/
theorem K2Map_constantCoeff_K2Map_C (v : K2 I R) :
    K2Map (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R)
      (K2Map (MvPolynomial.C : R →+* MvPolynomial σ R) v) = v := by
  apply Subtype.ext
  rw [K2Map_apply, K2Map_apply, ringMap_ringMap, MvPolynomial.constantCoeff_comp_C]
  exact DFunLike.congr_fun (ringMap_id (I := I) (R := R)) (v : SteinbergGroup I R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_constantCoeff_K2Map_C

/-- The constants `K₂(I, R) → K₂(I, R[σ])` are injective. -/
theorem K2Map_C_injective :
    Function.Injective (K2Map (I := I) (MvPolynomial.C : R →+* MvPolynomial σ R)) := by
  intro a b hab
  have h := DFunLike.congr_arg
    (K2Map (I := I) (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R)) hab
  rwa [K2Map_constantCoeff_K2Map_C, K2Map_constantCoeff_K2Map_C] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_C_injective

/-- The splitting: `(C (ev₀ u))⁻¹ * u` is killed by `ev₀`. -/
theorem K2Map_constantCoeff_split (u : K2 I (MvPolynomial σ R)) :
    K2Map (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R)
      ((K2Map (MvPolynomial.C : R →+* MvPolynomial σ R)
        (K2Map (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) u))⁻¹ * u) = 1 := by
  rw [map_mul, map_inv, K2Map_constantCoeff_K2Map_C, inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_constantCoeff_split

/-- With no variables, `ev₀ : K₂(I, R[σ]) → K₂(I, R)` is injective. -/
theorem K2Map_constantCoeff_injective_of_isEmpty [IsEmpty σ] :
    Function.Injective (K2Map (I := I) (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R)) := by
  have hinj := ringMap_injective_of_leftInverse (I := I)
    (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) MvPolynomial.C
    fun x ↦ (MvPolynomial.eq_C_of_isEmpty x).symm
  intro a b hab
  have h2 := congrArg Subtype.val hab
  rw [K2Map_apply, K2Map_apply] at h2
  exact Subtype.ext (hinj h2)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_constantCoeff_injective_of_isEmpty

/-- With no variables, an element of `K₂(I, R[σ])` killed by `ev₀` is trivial. -/
theorem eq_one_of_K2Map_constantCoeff_eq_one [IsEmpty σ] {u : K2 I (MvPolynomial σ R)}
    (hu : K2Map (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R) u = 1) : u = 1 :=
  K2Map_constantCoeff_injective_of_isEmpty (by rw [hu, map_one])

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.eq_one_of_K2Map_constantCoeff_eq_one

end Retraction

/-- **The nil part of homotopy invariance**, all `k`: an element of `K₂(N, F_p[s_1..s_k])`
killed by evaluation at `0` dies after padding. -/
def PolyK2NilStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := MvPolynomial (Fin k) (ZMod p)) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilStatement

/-- **The isolated gap**: the nil part for `k ≥ 1`. -/
def PolyK2NilPosStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 0 < k → k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 →
        ∃ M : ℕ, ∃ hNM : N ≤ M,
          K2IndexMap (R := MvPolynomial (Fin k) (ZMod p)) (Fin.castLEEmb hNM) u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilPosStatement

/-- The case `k = 0` of the nil part holds with `M = N`. -/
theorem polyK2Nil_of_pos (h : PolyK2NilPosStatement) : PolyK2NilStatement := by
  intro p hp k N hkN h5N u hu
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨N, le_rfl, ?_⟩
    rw [eq_one_of_K2Map_constantCoeff_eq_one hu, map_one]
  · exact h p hp k N hk hkN h5N u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2Nil_of_pos

/-- The nil part gives homotopy invariance, through the splitting `u = C(ev₀ u) · w`. -/
theorem polyK2Homotopy_of_nil (h : PolyK2NilStatement) : PolyK2HomotopyStatement := by
  intro p hp k N hkN h5N u
  obtain ⟨M, hNM, hM⟩ := h p hp k N hkN h5N _ (K2Map_constantCoeff_split u)
  refine ⟨M, hNM, K2IndexMap (Fin.castLEEmb hNM)
    (K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u), ?_⟩
  rw [map_mul, map_inv, inv_mul_eq_one] at hM
  rw [← hM, K2IndexMap_K2Map]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2Homotopy_of_nil

/-- Conversely, homotopy invariance gives the nil part, so `PolyK2NilStatement` is not
logically stronger than `PolyK2HomotopyStatement`. -/
theorem polyK2Nil_of_homotopy (h : PolyK2HomotopyStatement) : PolyK2NilStatement := by
  intro p hp k N hkN h5N u hu
  obtain ⟨M, hNM, v, huv⟩ := h p hp k N hkN h5N u
  refine ⟨M, hNM, ?_⟩
  have h2 := DFunLike.congr_arg
    (K2Map (I := Fin M) (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p))
    huv
  rw [K2Map_constantCoeff_K2Map_C, ← K2IndexMap_K2Map, hu, map_one] at h2
  rw [huv, ← h2, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2Nil_of_homotopy

end GroupApproximation.BooneHigman.Metabelian.ElemFP
