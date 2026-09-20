import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresElt
import GroupApproximation.Steinberg.Functoriality

/-!
# The kernel of `St(B) → St(C)` for a surjection `B → C` (k2-poly H.L1)

For a surjective ring map `ρ : B →+* C`:
* `ker_ringMap_le`: `ker(St(B) → St(C))` lies in the normal closure of the `x_ij(a)`, `a ∈ ker ρ`.
  Lifting generators through `ρ` gives `St(C) → St(B) ⧸ ⟨⟨x_ij(ker ρ)⟩⟩`, and it inverts the quotient
  map.
* `normalClosure_le_range_can`: with van der Kallen's elements over `B`, that normal closure lies in
  the image of Tulenbaev's relative group `St(B, 𝔄)`, for `𝔄 ⊇ ker ρ`. The image is normal
  (`RelPres.elt_conj`), and `x_ij(a) = X(eᵢ, a eⱼ)`.
* `ker_ringMap_le_range_can`: the two together.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found
open GroupApproximation.BooneHigmanLinear.K2Found.RelPres (RMem RelSt X can)

variable {I B C : Type*} [Fintype I] [DecidableEq I] [CommRing B] [CommRing C]

/-- The `x_ij(a)` with `a ∈ 𝔄`. -/
def xSet (𝔄 : Ideal B) : Set (SteinbergGroup I B) :=
  {g | ∃ (i j : I) (hij : i ≠ j) (a : B), a ∈ 𝔄 ∧ x i j hij a = g}

theorem x_mem_normalClosure {𝔄 : Ideal B} {i j : I} (hij : i ≠ j) {a : B} (ha : a ∈ 𝔄) :
    x i j hij a ∈ Subgroup.normalClosure (xSet (I := I) 𝔄) :=
  Subgroup.subset_normalClosure ⟨i, j, hij, a, ha, rfl⟩

/-- The quotient of `St(B)` by the normal closure of the `x_ij(ker ρ)`. -/
abbrev QSt (ρ : B →+* C) : Type _ :=
  SteinbergGroup I B ⧸ Subgroup.normalClosure (xSet (I := I) (RingHom.ker ρ))

/-- Lifting the generators of `St(C)` through a surjection `ρ`. -/
noncomputable def liftQ (ρ : B →+* C) (hρ : Function.Surjective ρ) :
    SteinbergGroup I C →* QSt (I := I) ρ :=
  PresentedGroup.toGroup
    (f := fun g : SteinbergGenerator I C =>
      (QuotientGroup.mk (x g.row g.column g.row_ne_column (Function.surjInv hρ g.coefficient)) :
        QSt (I := I) ρ)) (by
    intro w hw
    change IsRelation w at hw
    have hl : ∀ c, ρ (Function.surjInv hρ c) = c := Function.surjInv_eq hρ
    have hker : ∀ {i j : I} (hij : i ≠ j) (d : B), ρ d = 0 →
        (QuotientGroup.mk (x i j hij d) : QSt (I := I) ρ) = 1 := by
      intro i j hij d hd
      exact (QuotientGroup.eq_one_iff _).2 (x_mem_normalClosure hij (RingHom.mem_ker.2 hd))
    cases hw with
    | add i j hij a b =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        change (QuotientGroup.mk (x i j hij (Function.surjInv hρ a)) : QSt (I := I) ρ) *
            QuotientGroup.mk (x i j hij (Function.surjInv hρ b)) *
              (QuotientGroup.mk (x i j hij (Function.surjInv hρ (a + b))))⁻¹ = 1
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, x_mul, ← x_neg,
          x_mul]
        refine hker hij _ ?_
        rw [map_add, map_add, map_neg, hl, hl, hl, add_neg_cancel]
    | commute i j k l hij hkl hjk hli a b =>
        simp only [map_commutatorElement, FreeGroup.lift_apply_of]
        change ⁅(QuotientGroup.mk (x i j hij (Function.surjInv hρ a)) : QSt (I := I) ρ),
          QuotientGroup.mk (x k l hkl (Function.surjInv hρ b))⁆ = 1
        rw [commutatorElement_eq_one_iff_mul_comm, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (x_commute_of_ne i j k l hij hkl hjk hli _ _).eq]
    | adjacent i j k hij hjk hik a b =>
        simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
        change ⁅(QuotientGroup.mk (x i j hij (Function.surjInv hρ a)) : QSt (I := I) ρ),
            QuotientGroup.mk (x j k hjk (Function.surjInv hρ b))⁆ *
          (QuotientGroup.mk (x i k hik (Function.surjInv hρ (a * b))))⁻¹ = 1
        have e : ⁅(QuotientGroup.mk (x i j hij (Function.surjInv hρ a)) : QSt (I := I) ρ),
            QuotientGroup.mk (x j k hjk (Function.surjInv hρ b))⁆ =
            QuotientGroup.mk ⁅x i j hij (Function.surjInv hρ a), x j k hjk (Function.surjInv hρ b)⁆ :=
          (map_commutatorElement (QuotientGroup.mk' _) _ _).symm
        rw [e, x_commutator, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← x_neg, x_mul]
        refine hker hik _ ?_
        rw [map_add, map_neg, map_mul, hl, hl, hl, add_neg_cancel])

theorem liftQ_x (ρ : B →+* C) (hρ : Function.Surjective ρ) {i j : I} (hij : i ≠ j) (c : C) :
    liftQ ρ hρ (x i j hij c) = QuotientGroup.mk (x i j hij (Function.surjInv hρ c)) :=
  PresentedGroup.toGroup.of _

/-- `liftQ ∘ ringMap ρ` is the quotient map. -/
theorem liftQ_comp_ringMap (ρ : B →+* C) (hρ : Function.Surjective ρ) :
    (liftQ ρ hρ).comp (ringMap (I := I) ρ) = QuotientGroup.mk' _ := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, b⟩
  change liftQ ρ hρ (ringMap ρ (x i j hij b)) = QuotientGroup.mk (x i j hij b)
  rw [ringMap_x, liftQ_x, QuotientGroup.eq]
  refine Subgroup.subset_normalClosure ⟨i, j, hij, -Function.surjInv hρ (ρ b) + b, ?_, ?_⟩
  · rw [RingHom.mem_ker, map_add, map_neg, Function.surjInv_eq hρ, neg_add_cancel]
  · rw [← x_mul, x_neg]

#audit_axioms liftQ_comp_ringMap

/-- **The kernel of `St(B) → St(C)`** lies in the normal closure of the `x_ij(ker ρ)`. -/
theorem ker_ringMap_le (ρ : B →+* C) (hρ : Function.Surjective ρ) :
    (ringMap (I := I) ρ).ker ≤ Subgroup.normalClosure (xSet (I := I) (RingHom.ker ρ)) := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h := DFunLike.congr_fun (liftQ_comp_ringMap (I := I) ρ hρ) g
  simp only [MonoidHom.comp_apply, hg, map_one] at h
  exact (QuotientGroup.eq_one_iff g).1 h.symm

#audit_axioms ker_ringMap_le

variable (hX : VdK.Elements I B)

/-- The `γ` whose image stays in the range under every conjugation. -/
def conjStable (𝔄 : Ideal B) : Subgroup (RelSt I B 𝔄) :=
    { carrier := {γ | ∀ y : SteinbergGroup I B, y * can hX 𝔄 γ * y⁻¹ ∈ (can hX 𝔄).range}
      one_mem' := by
        intro y
        rw [map_one, mul_one, mul_inv_cancel]
        exact one_mem _
      mul_mem' := by
        intro a b ha hb y
        have e : y * can hX 𝔄 (a * b) * y⁻¹ =
            (y * can hX 𝔄 a * y⁻¹) * (y * can hX 𝔄 b * y⁻¹) := by rw [map_mul]; group
        rw [e]
        exact mul_mem (ha y) (hb y)
      inv_mem' := by
        intro a ha y
        have e : y * can hX 𝔄 a⁻¹ * y⁻¹ = (y * can hX 𝔄 a * y⁻¹)⁻¹ := by rw [map_inv]; group
        rw [e]
        exact inv_mem (ha y) }

/-- The image of the relative group is normal. -/
theorem range_can_normal (𝔄 : Ideal B) : (can hX 𝔄).range.Normal := by
  refine ⟨fun g hg y => ?_⟩
  obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hg
  have hS : ∀ γ, γ ∈ conjStable hX 𝔄 := fun γ =>
    PresentedGroup.generated_by _ (conjStable hX 𝔄) (fun g => by
      intro y
      obtain ⟨p, hp⟩ := g
      change y * can hX 𝔄 (X p hp) * y⁻¹ ∈ (can hX 𝔄).range
      rw [RelPres.can_X, RelPres.elt_conj]
      exact MonoidHom.mem_range.2 ⟨X _ (RelPres.smulPair_mem (projection y).2 hp),
        (RelPres.can_X hX 𝔄 _ _).trans (RelPres.elt_congr hX rfl _ _)⟩) γ
  exact hS γ y

/-- `x_ij(a) = X(eᵢ, a eⱼ)` lies in the image of `St(B, 𝔄)` for `a ∈ 𝔄`. -/
theorem x_mem_range_can {𝔄 : Ideal B} {i j : I} (hij : i ≠ j) {a : B} (ha : a ∈ 𝔄) :
    x i j hij a ∈ (can hX 𝔄).range := by
  have hp : RMem 𝔄 (Pi.single i (1 : B), Pi.single j a) := by
    refine ⟨RelPres.isEColumn_single i, fun k => ?_, ?_⟩
    · by_cases hk : k = j
      · rw [hk, Pi.single_eq_same]
        exact ha
      · rw [Pi.single_eq_of_ne hk]
        exact 𝔄.zero_mem
    · change (Pi.single j a : I → B) ⬝ᵥ Pi.single i 1 = 0
      rw [dotProduct_single, Pi.single_eq_of_ne hij, zero_mul]
  refine MonoidHom.mem_range.2 ⟨X _ hp, ?_⟩
  rw [RelPres.can_X]
  exact hX.std i j hij a

theorem normalClosure_le_range_can {𝔄 𝔅 : Ideal B} (h : 𝔅 ≤ 𝔄) :
    Subgroup.normalClosure (xSet (I := I) 𝔅) ≤ (can hX 𝔄).range := by
  haveI := range_can_normal hX 𝔄
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨i, j, hij, a, ha, rfl⟩
  exact x_mem_range_can hX hij (h ha)

/-- **The kernel of `St(B) → St(C)`** is in the image of `St(B, 𝔄)`, for `ker ρ ≤ 𝔄`. -/
theorem ker_ringMap_le_range_can (ρ : B →+* C) (hρ : Function.Surjective ρ) {𝔄 : Ideal B}
    (h : RingHom.ker ρ ≤ 𝔄) : (ringMap (I := I) ρ).ker ≤ (can hX 𝔄).range :=
  (ker_ringMap_le ρ hρ).trans (normalClosure_le_range_can hX h)

#audit_axioms ker_ringMap_le_range_can

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
