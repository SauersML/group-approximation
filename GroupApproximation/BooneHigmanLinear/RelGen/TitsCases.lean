import GroupApproximation.BooneHigmanLinear.RelGen.Defs
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein–Tits–Vaserstein, part 1: conjugating `x(J)` and `z_ab` by one root element

Lane bh-pal-wire, k2-poly H.L3 (L–S Theorem 4.2 in type A). Let `J` be an ideal and let
`g = x_kl(η)` be a root element.

* `conj_x_mem_xGroup`: if `(k, l) ≠ (d, c)`, then `g x_cd(s) g⁻¹ ∈ St(Φ, J)` for `s ∈ J`. By
  commutation or the commutator relation.
* `conj_ba_mem`: conjugation by `x_ba(ζ)` maps `St(Φ, J)` into `𝒵_ab = ⟨x(J), z_ab(J, ·)⟩`.
  On the generator `x_ab(s)` it gives `z_ab(s, -ζ)`.
* `conj_z_mem`: if `(k, l) ≠ (a, b)`, then `g z_ab(s, ζ) g⁻¹ ∈ 𝒵_ab`. The four cases:
  * `(k, l) = (b, a)` shifts `ζ`;
  * `g` commuting with `x_ba` reduces to `conj_ba_mem`;
  * `l = b` and `k = a` move `g` past `x_ba` at the cost of a root element that does commute with
    `x_ba`.
The remaining case `(k, l) = (a, b)` needs a third index (`RelGen.Tits`).
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] {J : Ideal R}

theorem conj_eq_commutator_mul {G : Type*} [Group G] (g y : G) : g * y * g⁻¹ = ⁅g, y⁆ * y := by
  rw [commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_eq_commutator_mul

theorem x_mem_xGroup {i j : I} (hij : i ≠ j) {s : R} (hs : s ∈ J) : x i j hij s ∈ xGroup I J :=
  Subgroup.subset_closure ⟨i, j, hij, s, hs, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_mem_xGroup

theorem xGroup_le_zGen (U : I → I → Prop) : xGroup I J ≤ zGen I J U :=
  Subgroup.closure_mono Set.subset_union_left

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.xGroup_le_zGen

theorem z_mem_zGen {U : I → I → Prop} {a b : I} (hab : a ≠ b) (hU : U a b) {s : R} (hs : s ∈ J)
    (ξ : R) : zElt a b hab s ξ ∈ zGen I J U :=
  Subgroup.subset_closure (Or.inr ⟨a, b, hab, s, ξ, hU, hs, rfl⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.z_mem_zGen

theorem zGen_mono {U V : I → I → Prop} (hUV : ∀ i j, U i j → V i j) : zGen I J U ≤ zGen I J V := by
  refine Subgroup.closure_mono (Set.union_subset_union_right _ ?_)
  rintro _ ⟨i, j, hij, s, ξ, hU, hs, rfl⟩
  exact ⟨i, j, hij, s, ξ, hUV i j hU, hs, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zGen_mono

/-- `z_ab(s, ξ) = X x_ab(s) X⁻¹` with `X = x_ba(-ξ)`. -/
theorem zElt_eq_conj {a b : I} (hab : a ≠ b) (s ξ : R) :
    zElt a b hab s ξ = x b a hab.symm (-ξ) * x a b hab s * (x b a hab.symm (-ξ))⁻¹ := by
  rw [zElt, ← x_neg, neg_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zElt_eq_conj

theorem zElt_zero {a b : I} (hab : a ≠ b) (s : R) : zElt a b hab s 0 = x a b hab s := by
  simp only [zElt, neg_zero, x_zero, one_mul, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zElt_zero

/-- The commutator case `l = c` of `conj_x_mem_xGroup`. -/
theorem conj_x_mem_xGroup_of_eq_left {k l d : I} (hkl : k ≠ l) (hld : l ≠ d) (hkd : k ≠ d)
    (η : R) {s : R} (hs : s ∈ J) : x k l hkl η * x l d hld s * (x k l hkl η)⁻¹ ∈ xGroup I J := by
  rw [conj_eq_commutator_mul, x_commutator k l d hkl hld hkd]
  exact Subgroup.mul_mem _ (x_mem_xGroup hkd (J.mul_mem_left η hs)) (x_mem_xGroup hld hs)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_x_mem_xGroup_of_eq_left

/-- The commutator case `d = k` of `conj_x_mem_xGroup`. -/
theorem conj_x_mem_xGroup_of_eq_right {k l c : I} (hkl : k ≠ l) (hck : c ≠ k) (hcl : c ≠ l)
    (η : R) {s : R} (hs : s ∈ J) : x k l hkl η * x c k hck s * (x k l hkl η)⁻¹ ∈ xGroup I J := by
  rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator c k l hck hkl hcl, ← x_neg]
  exact Subgroup.mul_mem _ (x_mem_xGroup hcl (neg_mem (J.mul_mem_right η hs)))
    (x_mem_xGroup hck hs)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_x_mem_xGroup_of_eq_right

/-- **Conjugating a relative root.** If `(k, l) ≠ (d, c)`, then `x_kl(η) x_cd(s) x_kl(η)⁻¹` lies in
`St(Φ, J)` for `s ∈ J`. -/
theorem conj_x_mem_xGroup {k l c d : I} (hkl : k ≠ l) (hcd : c ≠ d) (η : R) {s : R} (hs : s ∈ J)
    (hne : ¬(c = l ∧ d = k)) : x k l hkl η * x c d hcd s * (x k l hkl η)⁻¹ ∈ xGroup I J := by
  by_cases h1 : l = c
  · subst h1
    exact conj_x_mem_xGroup_of_eq_left hkl hcd (fun e => hne ⟨rfl, e.symm⟩) η hs
  · by_cases h2 : d = k
    · subst h2
      exact conj_x_mem_xGroup_of_eq_right hkl hcd (fun e => h1 e.symm) η hs
    · rw [(x_commute_of_ne k l c d hkl hcd h1 h2 η s).eq, mul_inv_cancel_right]
      exact x_mem_xGroup hcd hs

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_x_mem_xGroup

/-- `x_ba(ζ) x_ab(s) x_ba(ζ)⁻¹ = z_ab(s, -ζ)`. -/
theorem conj_ba_x_ab {a b : I} (hab : a ≠ b) (hba : b ≠ a) (ζ : R) {s : R} (hs : s ∈ J) :
    x b a hba ζ * x a b hab s * (x b a hba ζ)⁻¹ ∈ zGen I J (fun i j => i = a ∧ j = b) := by
  have e : x b a hba ζ * x a b hab s * (x b a hba ζ)⁻¹ = zElt a b hab s (-ζ) := by
    rw [zElt, neg_neg, ← x_neg]
  rw [e]
  exact z_mem_zGen hab ⟨rfl, rfl⟩ hs _

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_ba_x_ab

/-- **Conjugation by `x_ba(ζ)`** maps `St(Φ, J)` into `𝒵_ab = ⟨x(J), z_ab(J, ·)⟩`. -/
theorem conj_ba_mem {a b : I} (hab : a ≠ b) (ζ : R) {g : SteinbergGroup I R}
    (hg : g ∈ xGroup I J) :
    x b a hab.symm ζ * g * (x b a hab.symm ζ)⁻¹ ∈ zGen I J (fun i j => i = a ∧ j = b) := by
  rw [xGroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨c, d, hcd, s, hs, rfl⟩ := hg
    by_cases hc : c = a ∧ d = b
    · obtain ⟨hca, hdb⟩ := hc
      subst hca
      subst hdb
      exact conj_ba_x_ab hcd hab.symm ζ hs
    · exact xGroup_le_zGen _ (conj_x_mem_xGroup hab.symm hcd ζ hs hc)
  | one => simp only [mul_one, mul_inv_cancel, Subgroup.one_mem]
  | mul g₁ g₂ _ _ h₁ h₂ =>
    rw [show x b a hab.symm ζ * (g₁ * g₂) * (x b a hab.symm ζ)⁻¹ =
      (x b a hab.symm ζ * g₁ * (x b a hab.symm ζ)⁻¹) *
        (x b a hab.symm ζ * g₂ * (x b a hab.symm ζ)⁻¹) by group]
    exact Subgroup.mul_mem _ h₁ h₂
  | inv g _ h =>
    rw [show x b a hab.symm ζ * g⁻¹ * (x b a hab.symm ζ)⁻¹ =
      (x b a hab.symm ζ * g * (x b a hab.symm ζ)⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ h

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_ba_mem

/-- The commuting case: `g` commutes with `X = x_ba(-ζ)` and `g ≠ x_ba`. -/
theorem conj_z_mem_of_commute {a b k l : I} (hab : a ≠ b) (hkl : k ≠ l) (η ζ : R) {s : R}
    (hs : s ∈ J) (hc : Commute (x k l hkl η) (x b a hab.symm (-ζ))) (hne : ¬(a = l ∧ b = k)) :
    x k l hkl η * zElt a b hab s ζ * (x k l hkl η)⁻¹ ∈
      zGen I J (fun i j => i = a ∧ j = b) := by
  have hX : x k l hkl η * x b a hab.symm (-ζ) * (x k l hkl η)⁻¹ = x b a hab.symm (-ζ) := by
    rw [hc.eq, mul_inv_cancel_right]
  have e : x k l hkl η * zElt a b hab s ζ * (x k l hkl η)⁻¹ =
      x b a hab.symm (-ζ) * (x k l hkl η * x a b hab s * (x k l hkl η)⁻¹) *
        (x b a hab.symm (-ζ))⁻¹ := by
    rw [zElt_eq_conj]
    calc x k l hkl η * (x b a hab.symm (-ζ) * x a b hab s * (x b a hab.symm (-ζ))⁻¹) *
          (x k l hkl η)⁻¹
        = (x k l hkl η * x b a hab.symm (-ζ) * (x k l hkl η)⁻¹) *
            (x k l hkl η * x a b hab s * (x k l hkl η)⁻¹) *
            (x k l hkl η * x b a hab.symm (-ζ) * (x k l hkl η)⁻¹)⁻¹ := by group
      _ = _ := by rw [hX]
  rw [e]
  exact conj_ba_mem hab (-ζ) (conj_x_mem_xGroup hkl hab η hs hne)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_z_mem_of_commute

/-- The case `(k, l) = (b, a)`: `x_ba(η) z_ab(s, ζ) x_ba(η)⁻¹ = z_ab(s, ζ - η)`. -/
theorem conj_z_mem_of_opp {a b : I} (hab : a ≠ b) (hba : b ≠ a) (η ζ : R) {s : R} (hs : s ∈ J) :
    x b a hba η * zElt a b hab s ζ * (x b a hba η)⁻¹ ∈ zGen I J (fun i j => i = a ∧ j = b) := by
  have e : x b a hba η * zElt a b hab s ζ * (x b a hba η)⁻¹ = zElt a b hab s (ζ - η) := by
    rw [zElt, zElt, ← x_neg]
    calc x b a hba η * (x b a hab.symm (-ζ) * x a b hab s * x b a hab.symm ζ) * x b a hba (-η)
        = (x b a hba η * x b a hab.symm (-ζ)) * x a b hab s *
            (x b a hab.symm ζ * x b a hba (-η)) := by group
      _ = x b a hab.symm (-(ζ - η)) * x a b hab s * x b a hab.symm (ζ - η) := by
        rw [x_mul, x_mul, show η + -ζ = -(ζ - η) by ring, show ζ + -η = ζ - η by ring]
  rw [e]
  exact z_mem_zGen hab ⟨rfl, rfl⟩ hs _

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_z_mem_of_opp

/-- The case `l = b`, `k ∉ {a, b}`: `x_kb(η)` moves past `x_ba` at the cost of `x_ka`. -/
theorem conj_z_mem_of_col {a b k : I} (hab : a ≠ b) (hkb : k ≠ b) (hka : k ≠ a) (η ζ : R) {s : R}
    (hs : s ∈ J) :
    x k b hkb η * zElt a b hab s ζ * (x k b hkb η)⁻¹ ∈ zGen I J (fun i j => i = a ∧ j = b) := by
  have hY : x k b hkb η * x a b hab s * (x k b hkb η)⁻¹ = x a b hab s := by
    rw [(x_commute_of_ne k b a b hkb hab hab.symm hkb.symm η s).eq, mul_inv_cancel_right]
  have hX : x k b hkb η * x b a hab.symm (-ζ) * (x k b hkb η)⁻¹ =
      x k a hka (η * -ζ) * x b a hab.symm (-ζ) := by
    rw [conj_eq_commutator_mul, x_commutator k b a hkb hab.symm hka]
  have e : x k b hkb η * zElt a b hab s ζ * (x k b hkb η)⁻¹ =
      x k a hka (η * -ζ) * zElt a b hab s ζ * (x k a hka (η * -ζ))⁻¹ := by
    rw [zElt_eq_conj]
    calc x k b hkb η * (x b a hab.symm (-ζ) * x a b hab s * (x b a hab.symm (-ζ))⁻¹) *
          (x k b hkb η)⁻¹
        = (x k b hkb η * x b a hab.symm (-ζ) * (x k b hkb η)⁻¹) *
            (x k b hkb η * x a b hab s * (x k b hkb η)⁻¹) *
            (x k b hkb η * x b a hab.symm (-ζ) * (x k b hkb η)⁻¹)⁻¹ := by group
      _ = _ := by rw [hX, hY]; group
  rw [e]
  exact conj_z_mem_of_commute hab hka _ ζ hs
    (x_commute_of_ne k a b a hka hab.symm hab hka.symm _ (-ζ)) (fun h => hkb h.2.symm)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_z_mem_of_col

/-- The case `k = a`, `l ∉ {a, b}`: `x_al(η)` moves past `x_ba` at the cost of `x_bl`. -/
theorem conj_z_mem_of_row {a b l : I} (hab : a ≠ b) (hal : a ≠ l) (hlb : l ≠ b) (η ζ : R) {s : R}
    (hs : s ∈ J) :
    x a l hal η * zElt a b hab s ζ * (x a l hal η)⁻¹ ∈ zGen I J (fun i j => i = a ∧ j = b) := by
  have hbl : b ≠ l := hlb.symm
  have hY : x a l hal η * x a b hab s * (x a l hal η)⁻¹ = x a b hab s := by
    rw [(x_commute_of_ne a l a b hal hab hal.symm hab.symm η s).eq, mul_inv_cancel_right]
  have hX : x a l hal η * x b a hab.symm (-ζ) * (x a l hal η)⁻¹ =
      x b l hbl (-(-ζ * η)) * x b a hab.symm (-ζ) := by
    rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator b a l hab.symm hal hbl,
      ← x_neg]
  have e : x a l hal η * zElt a b hab s ζ * (x a l hal η)⁻¹ =
      x b l hbl (-(-ζ * η)) * zElt a b hab s ζ * (x b l hbl (-(-ζ * η)))⁻¹ := by
    rw [zElt_eq_conj]
    calc x a l hal η * (x b a hab.symm (-ζ) * x a b hab s * (x b a hab.symm (-ζ))⁻¹) *
          (x a l hal η)⁻¹
        = (x a l hal η * x b a hab.symm (-ζ) * (x a l hal η)⁻¹) *
            (x a l hal η * x a b hab s * (x a l hal η)⁻¹) *
            (x a l hal η * x b a hab.symm (-ζ) * (x a l hal η)⁻¹)⁻¹ := by group
      _ = _ := by rw [hX, hY]; group
  rw [e]
  exact conj_z_mem_of_commute hab hbl _ ζ hs
    (x_commute_of_ne b l b a hbl hab.symm hlb hab _ (-ζ)) (fun h => hal h.1)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_z_mem_of_row

/-- **Conjugating `z_ab` by a root element other than `x_ab`.** -/
theorem conj_z_mem {a b k l : I} (hab : a ≠ b) (hkl : k ≠ l) (η ζ : R) {s : R} (hs : s ∈ J)
    (hne : ¬(k = a ∧ l = b)) :
    x k l hkl η * zElt a b hab s ζ * (x k l hkl η)⁻¹ ∈ zGen I J (fun i j => i = a ∧ j = b) := by
  by_cases h1 : k = b ∧ l = a
  · obtain ⟨hkb, hla⟩ := h1
    subst hkb
    subst hla
    exact conj_z_mem_of_opp hab hkl η ζ hs
  · by_cases h2 : l ≠ b ∧ a ≠ k
    · exact conj_z_mem_of_commute hab hkl η ζ hs
        (x_commute_of_ne k l b a hkl hab.symm h2.1 h2.2 η (-ζ)) (fun h => h1 ⟨h.2.symm, h.1.symm⟩)
    · rcases not_and_or.mp h2 with h2 | h2
      · have hlb : l = b := not_not.mp h2
        subst hlb
        exact conj_z_mem_of_col hab hkl (fun e => hne ⟨e, rfl⟩) η ζ hs
      · have hak : a = k := not_not.mp h2
        subst hak
        exact conj_z_mem_of_row hab hkl (fun e => hne ⟨rfl, e⟩) η ζ hs

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_z_mem

end GroupApproximation.BooneHigmanLinear.RelGen
