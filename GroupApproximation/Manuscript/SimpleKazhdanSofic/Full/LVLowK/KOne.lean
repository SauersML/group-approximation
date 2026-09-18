import GroupApproximation.KOne.AllRanksElementary

/-!
# `K₁`-type vanishing for `L = L_k(1,2)`: perfectness and trivial abelianizations

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Q2). Khanh's Theorem 5.1
(arXiv:2609.08428) uses `K₁(L(1,2)) = 0` from Ara-Brustenga-Cortiñas. The repository
already proves the elementary-generation form:

* `BinaryLeavitt.elementaryGroup_eq_top`: `GL_n(L) = EL_n(L)` for `n ≥ 2`;
* `BinaryLeavitt.binaryLeavittUnits_perfect`: `Lˣ` is perfect;
* `Full.LVEGen.K1_trivial`, `Full.LVEGen.glN_eq_elementary`: the stable forms.

This file adds the "`GL(L)^ab` is trivial" form:

* `elementaryGroup_le_commutator`: over any ring, `EL_n ≤ [GL_n, GL_n]` for `n ≥ 3`;
* `commutator_eq_top_of_mulEquiv`: perfectness transfers along group isomorphisms;
* `abelianization_subsingleton_of_commutator_eq_top`: a perfect group has trivial
  abelianization;
* `binaryLeavittGL_perfect`: `[GL_n(L), GL_n(L)] = GL_n(L)` for every `n ≥ 2`;
* `binaryLeavittGL_abelianization_subsingleton`, `binaryLeavittUnits_abelianization_subsingleton`:
  `GL_n(L)^ab = 1` for `n ≥ 2`, and `(Lˣ)^ab = 1`.
-/

namespace GroupApproximation.Full.LVLowK

open scoped commutatorElement

/-- Given two indices of `Fin n` with `n ≥ 3`, a third index distinct from both. -/
private theorem exists_third {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ l : Fin n, i ≠ l ∧ l ≠ j := by
  obtain ⟨m, hm, hmi, hmj⟩ : ∃ m : ℕ, m < 3 ∧ m ≠ i.val ∧ m ≠ j.val := by
    by_cases hi0 : i.val = 0
    · by_cases hj1 : j.val = 1
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, by omega⟩
    · by_cases hj0 : j.val = 0
      · by_cases hi1 : i.val = 1
        · exact ⟨2, by omega, by omega, by omega⟩
        · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨0, by omega, by omega, by omega⟩
  exact ⟨⟨m, by omega⟩, fun h => hmi (congrArg Fin.val h).symm,
    fun h => hmj (congrArg Fin.val h)⟩

/-- **Elementary matrices are commutators in rank `≥ 3`**: over any ring, `EL_n ≤ [GL_n, GL_n]`
for `n ≥ 3`, by the Steinberg relation `e_{ij}(a) = [e_{il}(a), e_{lj}(1)]`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem elementaryGroup_le_commutator {R : Type*} [Ring R] (n : ℕ) (hn : 3 ≤ n) :
    elementaryGroup (Fin n) R ≤ commutator (Matrix (Fin n) (Fin n) R)ˣ := by
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  obtain ⟨l, hil, hlj⟩ := exists_third hn i j
  have hcomm : elementaryUnit i j hij a =
      ⁅elementaryUnit i l hil a, elementaryUnit l j hlj 1⁆ := by
    rw [elementaryUnit_commutator i l j hil hlj hij a 1, mul_one]
  show elementaryUnit i j hij a ∈ commutator (Matrix (Fin n) (Fin n) R)ˣ
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Perfectness transfers along a group isomorphism. -/
theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : commutator G = ⊤) : commutator H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hle : commutator G ≤ (commutator H).comap e.toMonoidHom := by
    rw [commutator_eq_closure G, Subgroup.closure_le]
    rintro _ ⟨p, q, rfl⟩
    show e ⁅p, q⁆ ∈ commutator H
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hmem : e.symm x ∈ commutator G := by
    rw [h]
    exact Subgroup.mem_top _
  have := hle hmem
  rw [Subgroup.mem_comap] at this
  simpa using this

/-- **A perfect group has trivial abelianization.** -/
theorem abelianization_subsingleton_of_commutator_eq_top {G : Type*} [Group G]
    (h : commutator G = ⊤) : Subsingleton (Abelianization G) := by
  have hone : ∀ x : Abelianization G, x = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    have hmem : a ∈ (Abelianization.of : G →* Abelianization G).ker := by
      rw [Abelianization.ker_of, h]
      exact Subgroup.mem_top a
    exact MonoidHom.mem_ker.mp hmem
  exact ⟨fun x y => (hone x).trans (hone y).symm⟩

section BinaryLeavitt

open BinaryLeavitt

variable (k : Type) [Field k]

/-- **`GL_n(L)` is perfect for every `n ≥ 2`**, `L = L_k(1,2)` over any field: rank `≥ 3` from
`GL_n = EL_n` and the Steinberg relation, rank two from `GL₂(L) ≅ Lˣ` (two-leaf prefix code) and
the perfectness of `Lˣ` (`simple_kazhdan_sofic_group.tex` l.733-735; Khanh arXiv:2609.08428,
Thm 5.1, input `K₁(L) = 0`). -/
theorem binaryLeavittGL_perfect (n : ℕ) (hn : 2 ≤ n) :
    commutator (Matrix (Fin n) (Fin n) (BinaryLeavittAlgebra k))ˣ = ⊤ := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · obtain rfl : n = 2 := by omega
    let e : (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ ≃* (BinaryLeavittAlgebra k)ˣ :=
      (BinaryLeavitt.family k).prefixUnitsEquiv (leftCombCode 1)
        ((BinaryLeavitt.family k).leftCombCode_complete 1)
    exact commutator_eq_top_of_mulEquiv e.symm (BinaryLeavitt.binaryLeavittUnits_perfect k)
  · exact eq_top_iff.mpr ((BinaryLeavitt.elementaryGroup_eq_top k n hn).symm.le.trans
      (elementaryGroup_le_commutator n hge))

/-- **`GL_n(L)^ab = 1`** for every `n ≥ 2`, `L = L_k(1,2)` over any field
(`simple_kazhdan_sofic_group.tex` l.733-735; Khanh arXiv:2609.08428, Thm 5.1). -/
theorem binaryLeavittGL_abelianization_subsingleton (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Abelianization (Matrix (Fin n) (Fin n) (BinaryLeavittAlgebra k))ˣ) :=
  abelianization_subsingleton_of_commutator_eq_top (binaryLeavittGL_perfect k n hn)

/-- **`(Lˣ)^ab = 1`** for `L = L_k(1,2)` over any field
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem binaryLeavittUnits_abelianization_subsingleton :
    Subsingleton (Abelianization (BinaryLeavittAlgebra k)ˣ) :=
  abelianization_subsingleton_of_commutator_eq_top (BinaryLeavitt.binaryLeavittUnits_perfect k)

end BinaryLeavitt

end GroupApproximation.Full.LVLowK
