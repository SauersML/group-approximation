import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Chain
import Mathlib.Tactic.Group

/-!
# Common right multiples along nested supports

Item 1 of `thompson-f-one-minus-x1-is-ore-with-every-element`: in `K[F]`, finitely many
`1 - g` with `g` conjugate to `x0^{±1}` or `x1^{±1}` have a nonzero common right multiple.

This is Step 2 of `thompson-f-one-minus-x1-is-ore-with-every-element-proof`, run against three
properties of a group `G` with elements `x0`, `x1` and a subgroup `H` (in `F`, `H = F_[1/2,1]`):
* `x1 ∈ H`, and `e : H ≃* G` with `e x1 = x0` (affine rescaling);
* conjugates of `H` are nested: `c H c⁻¹ ≤ H` or `c⁻¹ H c ≤ H` for every `c`;
* V. Guba's Theorem 3.18 for `x0`: every nonzero `b` has a right multiple `b v ≠ 0` in
  `(1 - x0) K[G]`.

* `exists_ne_zero_forall_mul_eq_of_isChain`: the ring-level induction along a chain of
  subsemirings, largest last.
* `ore_rangeS_of_mulEquiv`: Theorem 3.18 moved into the image of `K[L]` for `L ≃* G`.
* `exists_common_right_multiple_of_nested`: item 1 for the conjugacy classes of `x0^{±1}`
  and `x1^{±1}`.
-/

namespace GroupApproximation
namespace ThompsonOre

open MonoidAlgebra

section Chain

variable {R ι : Type*} [Semiring R]

/-- A finite nonempty family inside a chain has a largest member. -/
theorem exists_max_of_isChain {α : Type*} [Preorder α] {𝒜 : Set α}
    (h𝒜 : IsChain (· ≤ ·) 𝒜) (A : ι → α) (s : Finset ι) (hA : ∀ i ∈ s, A i ∈ 𝒜)
    (hs : s.Nonempty) : ∃ i₀ ∈ s, ∀ i ∈ s, A i ≤ A i₀ := by
  classical
  revert hA hs
  induction s using Finset.induction_on with
  | empty => intro _ hs; exact absurd hs Finset.not_nonempty_empty
  | insert j s hj ih =>
    intro hA _
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨j, Finset.mem_insert_self j _, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · simp at hi
    obtain ⟨m, hm, hmax⟩ := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)) hne
    rcases h𝒜.total (hA j (Finset.mem_insert_self j s)) (hA m (Finset.mem_insert_of_mem hm))
      with h | h
    · refine ⟨m, Finset.mem_insert_of_mem hm, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h
      · exact hmax i hi
    · refine ⟨j, Finset.mem_insert_self j s, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (hmax i hi).trans h

/-- **Common right multiples along a chain.** Suppose each `a i` absorbs a nonzero right
multiple of every nonzero `w ∈ A i` inside `A i`, and the `A i` lie in a chain. Then the `a i`
have a nonzero common right multiple, which lies in every upper bound of the `A i`. -/
theorem exists_ne_zero_forall_mul_eq_of_isChain [Nontrivial R] {𝒜 : Set (Subsemiring R)}
    (h𝒜 : IsChain (· ≤ ·) 𝒜) (a : ι → R) (A : ι → Subsemiring R) (s : Finset ι)
    (hA : ∀ i ∈ s, A i ∈ 𝒜)
    (hore : ∀ i ∈ s, ∀ w ∈ A i, w ≠ 0 → ∃ z ∈ A i, w * z ≠ 0 ∧ ∃ u, a i * u = w * z) :
    ∃ y : R, y ≠ 0 ∧ (∀ i ∈ s, ∃ u, a i * u = y) ∧
      ∀ C : Subsemiring R, (∀ i ∈ s, A i ≤ C) → y ∈ C := by
  classical
  revert hA hore
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hA hore
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨1, one_ne_zero, fun i hi => by simp at hi, fun C _ => one_mem C⟩
    obtain ⟨i₀, hi₀, hmax⟩ := exists_max_of_isChain h𝒜 A s hA hs
    obtain ⟨y, hy, hdiv, hC⟩ := ih (s.erase i₀) (Finset.erase_ssubset hi₀)
      (fun i hi => hA i (Finset.mem_of_mem_erase hi))
      (fun i hi => hore i (Finset.mem_of_mem_erase hi))
    have hyA : y ∈ A i₀ := hC (A i₀) fun i hi => hmax i (Finset.mem_of_mem_erase hi)
    obtain ⟨z, hz, hyz, u, hu⟩ := hore i₀ hi₀ y hyA hy
    refine ⟨y * z, hyz, fun i hi => ?_, fun C hC' => hC' i₀ hi₀ (mul_mem hyA hz)⟩
    by_cases h : i = i₀
    · subst h
      exact ⟨u, hu⟩
    · obtain ⟨u', hu'⟩ := hdiv i (Finset.mem_erase.mpr ⟨h, hi⟩)
      exact ⟨u' * z, by rw [← mul_assoc, hu']⟩

/-- `exists_ne_zero_forall_mul_eq_of_isChain` with the subsemirings chosen per index. -/
theorem exists_ne_zero_forall_mul_eq_of_isChain' [Nontrivial R] {𝒜 : Set (Subsemiring R)}
    (h𝒜 : IsChain (· ≤ ·) 𝒜) (a : ι → R) (s : Finset ι)
    (hore : ∀ i ∈ s, ∃ A ∈ 𝒜, ∀ w ∈ A, w ≠ 0 → ∃ z ∈ A, w * z ≠ 0 ∧ ∃ u, a i * u = w * z) :
    ∃ y : R, y ≠ 0 ∧ ∀ i ∈ s, ∃ u, a i * u = y := by
  choose! A hA hore using hore
  obtain ⟨y, hy, h, -⟩ := exists_ne_zero_forall_mul_eq_of_isChain h𝒜 a A s hA hore
  exact ⟨y, hy, h⟩

end Chain

section Transfer

variable {K G : Type*} [Ring K] [Group G]

/-- Theorem 3.18 for `x` gives it for `x⁻¹`, since `(1 - x⁻¹)(-x) = 1 - x`. -/
theorem ore_inv {x : G}
    (h : ∀ b : MonoidAlgebra K G, b ≠ 0 → ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K G x) * u) :
    ∀ b : MonoidAlgebra K G, b ≠ 0 →
      ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K G x⁻¹) * u := by
  intro b hb
  obtain ⟨v, hv, u, hu⟩ := h b hb
  have hx : (1 - of K G x⁻¹) * (-of K G x) = 1 - of K G x := by
    rw [mul_neg, sub_mul, one_mul, ← map_mul, inv_mul_cancel, map_one, neg_sub]
  exact ⟨v, hv, (-of K G x) * u, by rw [hu, ← mul_assoc, hx]⟩

/-- **Theorem 3.18 inside a subgroup.** If `ψ : L ≃* G` sends `g` to `x`, and `1 - x` has a
nonzero common right multiple with every nonzero element of `K[G]`, then `1 - g` absorbs a
nonzero right multiple of every nonzero `w` in the image of `K[L]`, inside that image. -/
theorem ore_rangeS_of_mulEquiv {x : G}
    (h : ∀ b : MonoidAlgebra K G, b ≠ 0 → ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K G x) * u)
    (L : Subgroup G) (ψ : L ≃* G) (g : L) (hg : ψ g = x) :
    ∀ w ∈ (mapDomainRingHom K L.subtype).rangeS, w ≠ 0 →
      ∃ z ∈ (mapDomainRingHom K L.subtype).rangeS, w * z ≠ 0 ∧
        ∃ u, (1 - of K G (g : G)) * u = w * z := by
  rintro _ ⟨w, rfl⟩ hw
  have hι : Function.Injective (mapDomainRingHom K L.subtype) :=
    mapDomain_injective Subtype.val_injective
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : MonoidAlgebra K L ≃+* MonoidAlgebra K G,
      Ψ = mapDomainRingEquiv K ψ := ⟨_, rfl⟩
  have hΨg : Ψ (of K L g) = of K G x := by
    rw [hΨ, of_apply, mapDomainRingEquiv_single, hg, of_apply]
  have hιg : mapDomainRingHom K L.subtype (of K L g) = of K G (g : G) := by
    simp [of_apply, mapDomain_single]
  have hw' : Ψ w ≠ 0 := fun h0 => hw (by
    rw [Ψ.injective (h0.trans (map_zero Ψ).symm), map_zero])
  obtain ⟨v, hv, u, hu⟩ := h (Ψ w) hw'
  have key : (1 - of K L g) * Ψ.symm u = w * Ψ.symm v := by
    apply Ψ.injective
    rw [map_mul, map_mul, map_sub, map_one, hΨg, Ψ.apply_symm_apply, Ψ.apply_symm_apply, hu]
  refine ⟨mapDomainRingHom K L.subtype (Ψ.symm v), ⟨_, rfl⟩, ?_,
    mapDomainRingHom K L.subtype (Ψ.symm u), ?_⟩
  · rw [← map_mul]
    intro h0
    apply hv
    have h1 : w * Ψ.symm v = 0 := hι (h0.trans (map_zero _).symm)
    calc Ψ w * v = Ψ (w * Ψ.symm v) := by rw [map_mul, Ψ.apply_symm_apply]
      _ = 0 := by rw [h1, map_zero]
  · rw [← hιg, ← map_one (mapDomainRingHom K L.subtype), ← map_sub, ← map_mul, ← map_mul, key]

end Transfer

section Nested

variable {K G : Type*} [Ring K] [Group G]

/-- Conjugation `x ↦ c x c⁻¹`, typed as a `MulEquiv` so that `MulEquiv.subgroupMap` applies
syntactically. -/
def conjEquiv (c : G) : G ≃* G := MulAut.conj c

theorem mem_map_conjEquiv {H : Subgroup G} {c f : G} :
    f ∈ H.map (conjEquiv c : G →* G) ↔ c⁻¹ * f * c ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : c⁻¹ * (conjEquiv c : G →* G) y * c = y := by
      show c⁻¹ * (c * y * c⁻¹) * c = y
      group
    rwa [h]
  · intro hf
    refine ⟨c⁻¹ * f * c, hf, ?_⟩
    show c * (c⁻¹ * f * c) * c⁻¹ = f
    group

theorem rangeS_mono {L₁ L₂ : Subgroup G} (h : L₁ ≤ L₂) :
    (mapDomainRingHom K L₁.subtype).rangeS ≤ (mapDomainRingHom K L₂.subtype).rangeS := by
  rintro _ ⟨w, rfl⟩
  refine ⟨mapDomainRingHom K (Subgroup.inclusion h) w, ?_⟩
  rw [← RingHom.comp_apply, ← mapDomainRingHom_comp]
  rfl

/-- The images of `K[G]` and of `K[c H c⁻¹]`, `c ∈ G`, form a chain when conjugates of `H` are
nested. -/
theorem isChain_rangeS_conj (H : Subgroup G)
    (hchain : ∀ c : G, (∀ f ∈ H, c * f * c⁻¹ ∈ H) ∨ (∀ f ∈ H, c⁻¹ * f * c ∈ H)) :
    IsChain (· ≤ ·) {A : Subsemiring (MonoidAlgebra K G) |
      A = (mapDomainRingHom K (⊤ : Subgroup G).subtype).rangeS ∨
        ∃ c : G, A = (mapDomainRingHom K (H.map (conjEquiv c : G →* G)).subtype).rangeS} := by
  rintro _ (rfl | ⟨c, rfl⟩) _ (rfl | ⟨d, rfl⟩) -
  · exact Or.inl le_rfl
  · exact Or.inr (rangeS_mono le_top)
  · exact Or.inl (rangeS_mono le_top)
  · rcases hchain (d⁻¹ * c) with h | h
    · refine Or.inl (rangeS_mono fun f hf => ?_)
      rw [mem_map_conjEquiv] at hf ⊢
      have e : d⁻¹ * f * d = (d⁻¹ * c) * (c⁻¹ * f * c) * (d⁻¹ * c)⁻¹ := by group
      rw [e]
      exact h _ hf
    · refine Or.inr (rangeS_mono fun f hf => ?_)
      rw [mem_map_conjEquiv] at hf ⊢
      have e : c⁻¹ * f * c = (d⁻¹ * c)⁻¹ * (d⁻¹ * f * d) * (d⁻¹ * c) := by group
      rw [e]
      exact h _ hf

variable (x0 x1 : G) (H : Subgroup G) (hx1 : x1 ∈ H) (e : H ≃* G) (he : e ⟨x1, hx1⟩ = x0)
  (h318 : ∀ b : MonoidAlgebra K G, b ≠ 0 → ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K G x0) * u)
include hx1 he h318

/-- Each `g ∈ C_+` absorbs right multiples inside some member of the chain: the whole group for
conjugates of `x0^{±1}`, and `c H c⁻¹` for `g = c x1^{±1} c⁻¹` (Step 1 of the route). -/
theorem exists_rangeS_ore {g : G}
    (hg : IsConj x0 g ∨ IsConj x0⁻¹ g ∨ IsConj x1 g ∨ IsConj x1⁻¹ g) :
    ∃ A ∈ {A : Subsemiring (MonoidAlgebra K G) |
      A = (mapDomainRingHom K (⊤ : Subgroup G).subtype).rangeS ∨
        ∃ c : G, A = (mapDomainRingHom K (H.map (conjEquiv c : G →* G)).subtype).rangeS},
      ∀ w ∈ A, w ≠ 0 → ∃ z ∈ A, w * z ≠ 0 ∧ ∃ u, (1 - of K G g) * u = w * z := by
  rcases hg with hg | hg | hg | hg <;> obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  · refine ⟨_, Or.inl rfl, ore_rangeS_of_mulEquiv h318 ⊤
      (Subgroup.topEquiv.trans (conjEquiv c).symm) ⟨c * x0 * c⁻¹, Subgroup.mem_top _⟩ ?_⟩
    show c⁻¹ * (c * x0 * c⁻¹) * c = x0
    group
  · refine ⟨_, Or.inl rfl, ore_rangeS_of_mulEquiv (ore_inv h318) ⊤
      (Subgroup.topEquiv.trans (conjEquiv c).symm) ⟨c * x0⁻¹ * c⁻¹, Subgroup.mem_top _⟩ ?_⟩
    show c⁻¹ * (c * x0⁻¹ * c⁻¹) * c = x0⁻¹
    group
  · have hm : c * x1 * c⁻¹ ∈ H.map (conjEquiv c : G →* G) :=
      mem_map_conjEquiv.mpr (by group; exact hx1)
    refine ⟨_, Or.inr ⟨c, rfl⟩, ore_rangeS_of_mulEquiv h318 _
      (((conjEquiv c).subgroupMap H).symm.trans e) ⟨_, hm⟩ ?_⟩
    have h1 : ((conjEquiv c).subgroupMap H).symm ⟨_, hm⟩ = ⟨x1, hx1⟩ :=
      Subtype.ext (show c⁻¹ * (c * x1 * c⁻¹) * c = x1 by group)
    rw [MulEquiv.trans_apply, h1, he]
  · have hm : c * x1⁻¹ * c⁻¹ ∈ H.map (conjEquiv c : G →* G) :=
      mem_map_conjEquiv.mpr (by
        rw [show c⁻¹ * (c * x1⁻¹ * c⁻¹) * c = x1⁻¹ by group]; exact H.inv_mem hx1)
    refine ⟨_, Or.inr ⟨c, rfl⟩, ore_rangeS_of_mulEquiv (ore_inv h318) _
      (((conjEquiv c).subgroupMap H).symm.trans e) ⟨_, hm⟩ ?_⟩
    have h1 : ((conjEquiv c).subgroupMap H).symm ⟨_, hm⟩ = (⟨x1, hx1⟩ : H)⁻¹ :=
      Subtype.ext (show c⁻¹ * (c * x1⁻¹ * c⁻¹) * c = x1⁻¹ by group)
    rw [MulEquiv.trans_apply, h1, map_inv, he]

/-- **Item 1 of `thompson-f-one-minus-x1-is-ore-with-every-element`, on the abstract data.**
Finitely many `1 - g`, each `g` conjugate to `x0^{±1}` or `x1^{±1}`, have a nonzero common right
multiple in `K[G]`. -/
theorem exists_common_right_multiple_of_nested [Nontrivial K]
    (hchain : ∀ c : G, (∀ f ∈ H, c * f * c⁻¹ ∈ H) ∨ (∀ f ∈ H, c⁻¹ * f * c ∈ H))
    (s : Finset G) (hs : ∀ g ∈ s, IsConj x0 g ∨ IsConj x0⁻¹ g ∨ IsConj x1 g ∨ IsConj x1⁻¹ g) :
    ∃ v : MonoidAlgebra K G, v ≠ 0 ∧ ∀ g ∈ s, ∃ y, (1 - of K G g) * y = v :=
  exists_ne_zero_forall_mul_eq_of_isChain' (isChain_rangeS_conj H hchain)
    (fun g => 1 - of K G g) s fun g hg => exists_rangeS_ore x0 x1 H hx1 e he h318 (hs g hg)

end Nested

end ThompsonOre
end GroupApproximation
