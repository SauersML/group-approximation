import GroupApproximation.BooneHigman.Metabelian.ElemFPKMIso
import GroupApproximation.Steinberg.QuotientExactness
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Rat.Cast.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leavitt resolvent ring and the finite presentation of its Steinberg groups

The Leavitt resolvent ring is

    R_L = ℤ⟨s₁, s₂, t₁, t₂, N, A |
             tᵢ sⱼ = δᵢⱼ,  s₁ t₁ + s₂ t₂ = 1,
             N s₁ = s₁ (N + 1),  N s₂ = 0,  A (N + 1) = 1 = (N + 1) A⟩,

six generators and nine relations.  This file

* defines `ResolventRing` as the quotient of the free algebra `ℤ⟨Fin 6⟩` by the two-sided
  ideal spanned by the nine relators, so that `R_L` is finitely presented by construction;
* proves that `St_{d+5}(R_L)` is finitely presented for every `d`
  (`steinberg_isFinitelyPresented`), by the rank-`≥ 5` finite presentation of the Steinberg
  group of a free algebra and the finite normal generation of the kernel of a Steinberg
  quotient map;
* proves, for any ring carrying the nine relations (`IsResolventTuple`), that every positive
  integer is a unit (`IsResolventTuple.natCast_isUnit`), so that `ℚ` maps to the ring
  (`IsResolventTuple.ratHom`) with central image (`IsResolventTuple.ratHom_commute`).

The unit computation is the one of the research node
`leavitt-resolvent-ring-is-fp-and-contains-q`: with `X = s₁^(m-1) s₂` one has
`(N + 1) X = m X`, hence `X = m A X`, and `u = t₂ t₁^(m-1) A X` satisfies `m u = 1`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open scoped commutatorElement

/-! ## The ring `R_L` -/

/-- The six generators of `ℤ⟨Fin 6⟩`, in the order `s₁, s₂, t₁, t₂, N, A`. -/
abbrev gen (i : Fin 6) : FreeAlgebra ℤ (Fin 6) := FreeAlgebra.ι ℤ i

/-- The nine relators of the Leavitt resolvent ring, as a list of elements that must vanish. -/
def resolventRelatorList : List (FreeAlgebra ℤ (Fin 6)) :=
  [gen 2 * gen 0 - 1, gen 2 * gen 1, gen 3 * gen 0, gen 3 * gen 1 - 1,
    gen 0 * gen 2 + gen 1 * gen 3 - 1,
    gen 4 * gen 0 - gen 0 * gen 4 - gen 0, gen 4 * gen 1,
    gen 5 * gen 4 + gen 5 - 1, gen 4 * gen 5 + gen 5 - 1]

/-- The set of the nine relators. -/
def resolventRelators : Set (FreeAlgebra ℤ (Fin 6)) :=
  {x | x ∈ resolventRelatorList}

theorem resolventRelators_finite : resolventRelators.Finite :=
  resolventRelatorList.finite_toSet

/-- The Leavitt resolvent ring `R_L`: six generators and nine relations over `ℤ`. -/
abbrev ResolventRing : Type :=
  (TwoSidedIdeal.span resolventRelators).ringCon.Quotient

/-- The quotient map `ℤ⟨Fin 6⟩ → R_L`. -/
def resolventMk : FreeAlgebra ℤ (Fin 6) →+* ResolventRing :=
  (TwoSidedIdeal.span resolventRelators).ringCon.mk'

theorem resolventMk_surjective : Function.Surjective resolventMk :=
  RingCon.mk'_surjective _

theorem ker_resolventMk :
    TwoSidedIdeal.ker resolventMk = TwoSidedIdeal.span resolventRelators :=
  TwoSidedIdeal.ker_ringCon_mk' _

/-! ## Finite presentation of `St_{d+5}(R_L)` -/

/-- `St_{d+5}(R_L)` is finitely presented for every `d`. -/
theorem steinberg_isFinitelyPresented (d : ℕ) :
    Group.IsFinitelyPresented (SteinbergGroup (Fin (d + 5)) ResolventRing) := by
  haveI := BooneHigman.Metabelian.ElemFP.steinbergFreeAlgebra_isFinitelyPresented (Fin 6) d
  exact Group.IsFinitelyPresented.of_surjective
    (SteinbergGroup.ringMap (I := Fin (d + 5)) resolventMk)
    (SteinbergGroup.ringMap_surjective_of_surjective resolventMk resolventMk_surjective)
    (SteinbergGroup.ringMap_ker_isFinitelyNormallyGenerated_of_ker_eq_span resolventMk
      resolventMk_surjective (by rw [Fintype.card_fin]; omega) resolventRelators
      resolventRelators_finite ker_resolventMk)

/-! ## Rings carrying the nine relations -/

/-- Six elements of a ring satisfying the nine resolvent relations. -/
structure IsResolventTuple {S : Type*} [Ring S] (s₁ s₂ t₁ t₂ N A : S) : Prop where
  t₁s₁ : t₁ * s₁ = 1
  t₁s₂ : t₁ * s₂ = 0
  t₂s₁ : t₂ * s₁ = 0
  t₂s₂ : t₂ * s₂ = 1
  sum : s₁ * t₁ + s₂ * t₂ = 1
  Ns₁ : N * s₁ = s₁ * (N + 1)
  Ns₂ : N * s₂ = 0
  AN : A * (N + 1) = 1
  NA : (N + 1) * A = 1

namespace IsResolventTuple

variable {S : Type*} [Ring S] {s₁ s₂ t₁ t₂ N A : S}

theorem N_mul_pow (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) (k : ℕ) :
    N * s₁ ^ k = s₁ ^ k * (N + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, add_mul, h.Ns₁, (Nat.cast_commute k s₁).eq,
      Nat.cast_succ]
    noncomm_ring

theorem t₁pow_mul_s₁pow (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) (k : ℕ) :
    t₁ ^ k * s₁ ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ, mul_assoc, ← mul_assoc (t₁ ^ k), ih, one_mul, h.t₁s₁]

/-- Every positive integer is a unit in a ring carrying the resolvent relations. -/
theorem natCast_isUnit (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) {m : ℕ} (hm : 0 < m) :
    IsUnit (m : S) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set X : S := s₁ ^ k * s₂ with hX
  have hNX : N * X = (k : S) * X := by
    rw [hX, ← mul_assoc, h.N_mul_pow k, mul_assoc, add_mul, h.Ns₂, zero_add,
      ← mul_assoc, ← (Nat.cast_commute k (s₁ ^ k)).eq, mul_assoc]
  have hX' : X = ((k + 1 : ℕ) : S) * (A * X) := by
    have h1 : (N + 1) * X = ((k + 1 : ℕ) : S) * X := by
      rw [add_mul, hNX, one_mul, Nat.cast_succ, add_mul, one_mul]
    calc X = A * (N + 1) * X := by rw [h.AN, one_mul]
      _ = A * (((k + 1 : ℕ) : S) * X) := by rw [mul_assoc, h1]
      _ = ((k + 1 : ℕ) : S) * (A * X) := by
        rw [← mul_assoc, ← (Nat.cast_commute (k + 1) A).eq, mul_assoc]
  set u : S := t₂ * t₁ ^ k * (A * X) with hu
  have hmu : ((k + 1 : ℕ) : S) * u = 1 := by
    rw [hu, ← mul_assoc, (Nat.cast_commute (k + 1) (t₂ * t₁ ^ k)).eq, mul_assoc, ← hX', hX,
      ← mul_assoc, mul_assoc t₂, h.t₁pow_mul_s₁pow k, mul_one, h.t₂s₂]
  have hum : u * ((k + 1 : ℕ) : S) = 1 := by
    rw [← (Nat.cast_commute (k + 1) u).eq, hmu]
  exact ⟨⟨_, u, hmu, hum⟩, rfl⟩

theorem intCast_isUnit (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) {z : ℤ} (hz : z ≠ 0) :
    IsUnit (z : S) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.cast_natCast]
    exact h.natCast_isUnit (Nat.pos_of_ne_zero (by rintro rfl; exact hz (by simp)))
  · rw [Int.cast_neg, Int.cast_natCast]
    exact (h.natCast_isUnit (Nat.pos_of_ne_zero (by rintro rfl; exact hz (by simp)))).neg

/-- The inverse of a nonzero integer is central. -/
theorem intCast_inv_mem_center {z : ℤ} (u : Sˣ) (hu : (u : S) = z) :
    ((u⁻¹ : Sˣ) : S) ∈ Subring.center S := by
  rw [Subring.mem_center_iff]
  intro x
  have hux : (u : S) * x = x * u := by rw [hu]; exact (Int.cast_commute z x).eq
  calc x * ↑u⁻¹ = ↑u⁻¹ * ↑u * x * ↑u⁻¹ := by rw [Units.inv_mul, one_mul]
    _ = ↑u⁻¹ * (↑u * x) * ↑u⁻¹ := by rw [mul_assoc (↑u⁻¹ : S) (↑u) x]
    _ = ↑u⁻¹ * (x * ↑u) * ↑u⁻¹ := by rw [hux]
    _ = ↑u⁻¹ * x * (↑u * ↑u⁻¹) := by simp only [mul_assoc]
    _ = ↑u⁻¹ * x := by rw [Units.mul_inv, mul_one]

/-- Every nonzero integer is a unit of the center. -/
theorem intCast_isUnit_center (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) {z : ℤ} (hz : z ≠ 0) :
    IsUnit (z : Subring.center S) := by
  obtain ⟨u, hu⟩ := h.intCast_isUnit hz
  have hv := intCast_inv_mem_center u hu
  refine ⟨⟨(z : Subring.center S), ⟨_, hv⟩, ?_, ?_⟩, rfl⟩ <;> apply Subtype.ext
  · change ((z : Subring.center S) : S) * ((u⁻¹ : Sˣ) : S) = 1
    rw [SubringClass.coe_intCast, ← hu, Units.mul_inv]
  · change ((u⁻¹ : Sˣ) : S) * ((z : Subring.center S) : S) = 1
    rw [SubringClass.coe_intCast, ← hu, Units.inv_mul]

/-- The ring homomorphism `ℚ → Z(S)` for a ring carrying the resolvent relations. -/
def ratHomCenter (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) : ℚ →+* Subring.center S :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := Int.castRingHom (Subring.center S))
    (fun y ↦ h.intCast_isUnit_center (nonZeroDivisors.coe_ne_zero y))

/-- The ring homomorphism `ℚ → S` for a ring carrying the resolvent relations. -/
def ratHom (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) : ℚ →+* S :=
  (Subring.center S).subtype.comp h.ratHomCenter

theorem ratHom_intCast (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) (z : ℤ) :
    h.ratHom (z : ℚ) = (z : S) :=
  map_intCast h.ratHom z

/-- The image of `ℚ` is central. -/
theorem ratHom_commute (h : IsResolventTuple s₁ s₂ t₁ t₂ N A) (q : ℚ) (x : S) :
    Commute (h.ratHom q) x :=
  (Subring.mem_center_iff.mp (h.ratHomCenter q).2 x).symm

end IsResolventTuple

/-! ## The generators of `R_L` satisfy the relations -/

/-- The image of the `i`-th generator in `R_L`. -/
abbrev rgen (i : Fin 6) : ResolventRing := resolventMk (gen i)

theorem resolventMk_relator {x : FreeAlgebra ℤ (Fin 6)} (hx : x ∈ resolventRelatorList) :
    resolventMk x = 0 := by
  rw [← TwoSidedIdeal.mem_ker, ker_resolventMk]
  exact TwoSidedIdeal.subset_span hx

theorem isResolventTuple :
    IsResolventTuple (rgen 0) (rgen 1) (rgen 2) (rgen 3) (rgen 4) (rgen 5) := by
  have r : ∀ x ∈ resolventRelatorList, resolventMk x = 0 := fun x hx ↦ resolventMk_relator hx
  simp only [resolventRelatorList, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, map_sub, map_mul, map_add, map_one] at r
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := r
  refine ⟨sub_eq_zero.mp h1, h2, h3, sub_eq_zero.mp h4, sub_eq_zero.mp h5, ?_, h7, ?_, ?_⟩
  · rw [mul_add, mul_one]; exact sub_eq_zero.mp (by rw [← h6]; abel)
  · rw [mul_add, mul_one]; exact sub_eq_zero.mp h8
  · rw [add_mul, one_mul]; exact sub_eq_zero.mp h9

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.steinberg_isFinitelyPresented
#audit_axioms GroupApproximation.SteinbergFP.IsResolventTuple.natCast_isUnit
#audit_axioms GroupApproximation.SteinbergFP.IsResolventTuple.ratHom_commute
#audit_axioms GroupApproximation.SteinbergFP.isResolventTuple
