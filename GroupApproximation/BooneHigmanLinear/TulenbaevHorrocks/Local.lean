import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Horrocks for `St_N` over a local ring: reduction to the relative core (lane pal-q111)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), Prop 4.3(a),
first step of the proof (p. 151).  Over a local ring `A` with residue field `k`:

* `stHorrocksAt_local_of_rel`: the Horrocks property of `St_N` over `A` (`StHorrocksAt A N`)
  follows from the Horrocks property over `k` and the **relative core**
  `StLocalRelHorrocksAt A N`, which is the same statement for elements trivial modulo `𝔪`.
  - Reduce `α ∈ St_N(A[X])` and `β ∈ St_N(A[X⁻¹])` modulo `𝔪`.  By the field case both become one
    constant `γ̄ ∈ St_N(k)`.
  - Lift `γ̄` to `γ ∈ St_N(A)`; then `α γ⁻¹` and `β γ⁻¹` are trivial modulo `𝔪` and have the same
    image in `St_N(A[X,X⁻¹])`.
* `stLocalHorrocksStatement_of`: `StLocalHorrocksStatementAt n₀` from the field case over every
  field (e.g. `stHorrocksAt_of_fieldNK`) and the relative core over every local ring.

The relative core is the content of T Lemmas 3.1–3.4 and Props 4.1, 4.3(a): an action of
`St_N(𝔪[X] + A[X⁻¹])` on `G × St_N(A[X⁻¹]) × (1 + 𝔪)` modulo `St_N(A, 𝔪)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic Polynomial
open GroupApproximation.BooneHigmanLinear.Tulenbaev

/-- Reduction modulo the maximal ideal, `A[X] → k[X]`. -/
noncomputable abbrev resPoly (A : Type) [CommRing A] [IsLocalRing A] :
    A[X] →+* (IsLocalRing.ResidueField A)[X] :=
  Polynomial.mapRingHom (IsLocalRing.residue A)

/-- **The relative core of T Prop 4.3(a)** over a local ring `A`, at rank `N`.  If `α ∈ St_N(A[X])`
and `β ∈ St_N(A[X⁻¹])` are trivial modulo the maximal ideal and have the same image in
`St_N(A[X,X⁻¹])`, then both come from one element of `St_N(A)`. -/
def StLocalRelHorrocksAt (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ) : Prop :=
  ∀ α β : SteinbergGroup (Fin N) A[X],
    ringMap (resPoly A) α = 1 → ringMap (resPoly A) β = 1 →
    ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) β →
      ∃ γ : SteinbergGroup (Fin N) A,
        ringMap (Polynomial.C : A →+* A[X]) γ = α ∧ ringMap (Polynomial.C : A →+* A[X]) γ = β

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalRelHorrocksAt

/-- **The relative core at every local ring**, ranks `N ≥ n₀`. -/
def StLocalRelHorrocksStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ), n₀ ≤ N → StLocalRelHorrocksAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalRelHorrocksStatementAt

/-- **T Prop 4.3(a), first step**: over a local ring, the Horrocks property of `St_N` follows from
the field case at the residue field and the relative core. -/
theorem stHorrocksAt_local_of_rel (A : Type) [CommRing A] [IsLocalRing A] {N : ℕ}
    (hk : StHorrocksAt (IsLocalRing.ResidueField A) N) (hrel : StLocalRelHorrocksAt A N) :
    StHorrocksAt A N := by
  have hresC : (resPoly A).comp (Polynomial.C : A →+* A[X]) =
      (Polynomial.C : IsLocalRing.ResidueField A →+* (IsLocalRing.ResidueField A)[X]).comp
        (IsLocalRing.residue A) :=
    Polynomial.mapRingHom_comp_C _
  have key : ∀ α β : SteinbergGroup (Fin N) A[X],
      ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) β →
        ∃ γ : SteinbergGroup (Fin N) A,
          ringMap (Polynomial.C : A →+* A[X]) γ = α ∧
            ringMap (Polynomial.C : A →+* A[X]) γ = β := by
    intro α β h
    have hbar : ringMap (toLaurentPos (IsLocalRing.ResidueField A)) (ringMap (resPoly A) α) =
        ringMap (toLaurentNeg (IsLocalRing.ResidueField A)) (ringMap (resPoly A) β) := by
      rw [ringMap_ringMap, ringMap_ringMap, ← laurentMap_comp_toLaurentPos,
        ← laurentMap_comp_toLaurentNeg, ← ringMap_ringMap, ← ringMap_ringMap, h]
    obtain ⟨γbar, hαbar, hβbar⟩ := hk.2.2 _ _ hbar
    obtain ⟨γ, hγ⟩ := ringMap_surjective_of_surjective (I := Fin N) (IsLocalRing.residue A)
      IsLocalRing.residue_surjective γbar
    obtain ⟨c, hcdef⟩ : ∃ c, ringMap (Polynomial.C : A →+* A[X]) γ = c := ⟨_, rfl⟩
    have hc : ringMap (resPoly A) c = ringMap (Polynomial.C : IsLocalRing.ResidueField A →+*
        (IsLocalRing.ResidueField A)[X]) γbar := by
      rw [← hcdef, ringMap_ringMap, hresC, ← ringMap_ringMap, hγ]
    have hcPN : ringMap (toLaurentPos A) c = ringMap (toLaurentNeg A) c := by
      rw [← hcdef, ringMap_ringMap, ringMap_ringMap, toLaurentPos_comp_C, toLaurentNeg_comp_C]
    have hα' : ringMap (resPoly A) (α * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hc, hαbar, mul_inv_cancel]
    have hβ' : ringMap (resPoly A) (β * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hc, hβbar, mul_inv_cancel]
    have hαβ' : ringMap (toLaurentPos A) (α * c⁻¹) = ringMap (toLaurentNeg A) (β * c⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv, h, hcPN]
    obtain ⟨δ, hδα, hδβ⟩ := hrel _ _ hα' hβ' hαβ'
    refine ⟨δ * γ, ?_, ?_⟩
    · rw [map_mul, hδα, hcdef, inv_mul_cancel_right]
    · rw [map_mul, hδβ, hcdef, inv_mul_cancel_right]
  refine ⟨?_, ?_, key⟩
  · refine (injective_iff_map_eq_one _).mpr fun α hα => ?_
    obtain ⟨γ, hγα, hγ1⟩ := key α 1 (by rw [hα, map_one])
    rw [← hγα, hγ1]
  · refine (injective_iff_map_eq_one _).mpr fun β hβ => ?_
    obtain ⟨γ, hγ1, hγβ⟩ := key 1 β (by rw [hβ, map_one])
    rw [← hγβ, hγ1]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_local_of_rel

/-! ### The relative core from its one-sided form -/

/-- **The one-sided relative core** (the content of T Prop 4.3(a), p. 151: "hence `β ∈ St_r(A)`").
If `α ∈ St_N(A[X])` is trivial modulo `𝔪` and has the same image in `St_N(A[X,X⁻¹])` as
`β ∈ St_N(A[X⁻¹])`, then `β` comes from `St_N(A)`. -/
def StLocalOneSidedAt (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ) : Prop :=
  ∀ α β : SteinbergGroup (Fin N) A[X], ringMap (resPoly A) α = 1 →
    ringMap (toLaurentPos A) α = ringMap (toLaurentNeg A) β →
      β ∈ (ringMap (I := Fin N) (Polynomial.C : A →+* A[X])).range

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalOneSidedAt

/-- The one-sided core at every local ring, ranks `N ≥ n₀`. -/
def StLocalOneSidedStatementAt (n₀ : ℕ) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (N : ℕ), n₀ ≤ N → StLocalOneSidedAt A N

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalOneSidedStatementAt

/-- `T ↦ T⁻¹` on `A[T,T⁻¹]`, as a ring map. -/
noncomputable def invertHom (A : Type) [CommRing A] :
    LaurentPolynomial A →+* LaurentPolynomial A :=
  (LaurentPolynomial.invert (R := A)).toRingEquiv.toRingHom

@[simp] theorem invertHom_apply {A : Type} [CommRing A] (f : LaurentPolynomial A) :
    invertHom A f = LaurentPolynomial.invert f := rfl

theorem invertHom_comp_toLaurentPos {A : Type} [CommRing A] :
    (invertHom A).comp (toLaurentPos A) = toLaurentNeg A := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [toLaurentPos, toLaurentNeg]
  · simp [toLaurentPos, toLaurentNeg]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.invertHom_comp_toLaurentPos

theorem invertHom_comp_toLaurentNeg {A : Type} [CommRing A] :
    (invertHom A).comp (toLaurentNeg A) = toLaurentPos A := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [toLaurentPos, toLaurentNeg]
  · simp [toLaurentPos, toLaurentNeg]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.invertHom_comp_toLaurentNeg

/-- **The relative core from the one-sided core**, applied once as stated and once after
`T ↦ T⁻¹` (Tulenbaev: "an analogous argument (with `X` replaced by `X⁻¹`) shows that `α`
also belongs to `St_r(A)`"). -/
theorem stLocalRelHorrocksAt_of_oneSided {A : Type} [CommRing A] [IsLocalRing A] {N : ℕ}
    (h : StLocalOneSidedAt A N) : StLocalRelHorrocksAt A N := by
  intro α β hα hβ hαβ
  obtain ⟨δ₁, hδ₁⟩ := MonoidHom.mem_range.mp (h α β hα hαβ)
  have hβα : ringMap (toLaurentPos A) β = ringMap (toLaurentNeg A) α := by
    have h' := congrArg (ringMap (invertHom A)) hαβ
    rw [ringMap_ringMap, ringMap_ringMap, invertHom_comp_toLaurentPos,
      invertHom_comp_toLaurentNeg] at h'
    exact h'.symm
  obtain ⟨δ₂, hδ₂⟩ := MonoidHom.mem_range.mp (h β α hβ hβα)
  have h12 : δ₁ = δ₂ := by
    apply ringMap_laurentC_injective N
    have e1 : ringMap (LaurentPolynomial.C : A →+* LaurentPolynomial A) δ₁ =
        ringMap (toLaurentNeg A) β := by
      rw [← hδ₁, ringMap_ringMap, toLaurentNeg_comp_C]
    have e2 : ringMap (LaurentPolynomial.C : A →+* LaurentPolynomial A) δ₂ =
        ringMap (toLaurentPos A) α := by
      rw [← hδ₂, ringMap_ringMap, toLaurentPos_comp_C]
    rw [e1, e2, hαβ]
  refine ⟨δ₂, hδ₂, ?_⟩
  rw [← h12]
  exact hδ₁

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stLocalRelHorrocksAt_of_oneSided

/-- The relative core at every local ring from the one-sided core. -/
theorem stLocalRelHorrocksStatement_of_oneSided {n₀ : ℕ}
    (h : StLocalOneSidedStatementAt n₀) :
    StLocalRelHorrocksStatementAt n₀ :=
  fun A _ _ N hN => stLocalRelHorrocksAt_of_oneSided (h A N hN)

#audit_axioms
  GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stLocalRelHorrocksStatement_of_oneSided

/-- **T Prop 4.3(a) at every local ring** from the field case at every field and the relative
core at every local ring. -/
theorem stLocalHorrocksStatement_of {n₀ : ℕ}
    (hF : ∀ (k : Type) [Field k] (N : ℕ), n₀ ≤ N → StHorrocksAt k N)
    (hrel : StLocalRelHorrocksStatementAt n₀) : StLocalHorrocksStatementAt n₀ :=
  fun A _ _ N hN => stHorrocksAt_local_of_rel A (hF _ N hN) (hrel A N hN)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stLocalHorrocksStatement_of

end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
