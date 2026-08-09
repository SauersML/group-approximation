import NonsoficGroupsExist.Steinberg.Perfect

/-!
# The Kervaire--Steinberg central-extension argument

This file formalizes the group-theoretic lifting argument behind the
Kervaire--Steinberg theorem.  It never assumes that the unstable Steinberg
kernel vanishes.  Instead, given an arbitrary central extension of a
Steinberg group, it begins constructing the canonical lifted root elements.

The first substantive step is the separated-root lemma: in a central
extension of `St_I(R)`, arbitrary lifts of two non-addable root elements
commute as soon as there is one index outside their four endpoints.  This is
the first paragraph of the classical splitting proof and is the mechanism
that makes the eventual lifted root elements independent of choices.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

namespace KervaireSteinberg

variable {Y I R : Type*} [Group Y] [Fintype I] [DecidableEq I] [Ring R]

/-- Four indices cannot exhaust `Fin n` when `n ≥ 5`. -/
theorem fin_exists_spare_index {n : ℕ} (hn : 5 ≤ n)
    (i j k l : Fin n) :
    ∃ t : Fin n, t ≠ i ∧ t ≠ j ∧ t ≠ k ∧ t ≠ l := by
  by_contra h
  push Not at h
  let s : Finset (Fin n) := {i, j, k, l}
  have hs : s = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    simp only [s, Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : t = i
    · exact Or.inl hi
    by_cases hj : t = j
    · exact Or.inr (Or.inl hj)
    by_cases hk : t = k
    · exact Or.inr (Or.inr (Or.inl hk))
    exact Or.inr (Or.inr (Or.inr (h t hi hj hk)))
  have hcard : n ≤ 4 := by
    have hle : s.card ≤ 4 := Finset.card_le_four
    rw [hs, Finset.card_fin] at hle
    exact hle
  omega

/-- If the commutators of `a` and `b` with `c` are central, then their
commutator commutes with `c`.  This is the three-subgroup calculation used in
the separated-root argument. -/
theorem commutator_commutes_of_commutators_mem_center
    {a b c : Y}
    (ha : ⁅c, a⁆ ∈ Subgroup.center Y)
    (hb : ⁅c, b⁆ ∈ Subgroup.center Y) :
    Commute ⁅a, b⁆ c := by
  have hba : ⁅b, c⁆ ∈ Subgroup.center Y := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center Y).inv_mem hb
  have hca : ⁅c, a⁆ ∈ Subgroup.center Y := ha
  have hsecond :
      ⁅⁅b, c⁆, c * a * c⁻¹⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hba (c * a * c⁻¹)).symm
  have hthird :
      ⁅⁅c, a⁆, a * b * a⁻¹⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp hca (a * b * a⁻¹)).symm
  have hhall := commutatorElement_commutatorElement_conj_mul a b c
  rw [hsecond, hthird, mul_one, mul_one] at hhall
  have hconj : Commute ⁅a, b⁆ (b * c * b⁻¹) :=
    commutatorElement_eq_one_iff_commute.mp hhall
  have hcentral : Commute ⁅a, b⁆ ⁅b, c⁆ := by
    change ⁅a, b⁆ * ⁅b, c⁆ = ⁅b, c⁆ * ⁅a, b⁆
    exact Subgroup.mem_center_iff.mp hba ⁅a, b⁆
  have hproduct : Commute ⁅a, b⁆ (⁅b, c⁆ * c) := by
    rw [← conj_eq_commutatorElement_mul, MulAut.conj_apply]
    exact hconj
  have hcancel : Commute ⁅a, b⁆ (⁅b, c⁆⁻¹ * (⁅b, c⁆ * c)) :=
    hcentral.inv_right.mul_right hproduct
  simpa only [inv_mul_cancel_left] using hcancel

/-- **Separated-root lifts commute.**  Let `Y → St_I(R)` be any central
extension.  If the two roots `(i,j)` and `(k,l)` are non-addable and `t` is
outside their four endpoints, then *every* pair of lifts of
`xᵢⱼ(r), xₖₗ(s)` commutes.

No injectivity of the Steinberg projection occurs here; `Y` is an arbitrary
central cover of the full presented Steinberg group. -/
theorem lifts_commute_of_spare_index
    (P : CentralExtension Y (SteinbergGroup I R))
    (i j k l t : I)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (htl : t ≠ l)
    (r s : R) (y z : Y)
    (hy : P.projection y = SteinbergGroup.x i j hij r)
    (hz : P.projection z = SteinbergGroup.x k l hkl s) :
    Commute y z := by
  obtain ⟨y', hy'⟩ := P.surjective (SteinbergGroup.x i t (Ne.symm hti) 1)
  obtain ⟨y'', hy''⟩ := P.surjective (SteinbergGroup.x t j htj r)
  have hleftImage :
      Commute (P.projection y') (P.projection z) := by
    rw [hy', hz]
    exact SteinbergGroup.x_commute_of_ne
      i t k l (Ne.symm hti) hkl htk hli 1 s
  have hrightImage :
      Commute (P.projection y'') (P.projection z) := by
    rw [hy'', hz]
    exact SteinbergGroup.x_commute_of_ne
      t j k l htj hkl hjk (Ne.symm htl) r s
  have hleftCenter : ⁅z, y'⁆ ∈ Subgroup.center Y := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center Y).inv_mem
      (P.commutator_mem_center hleftImage)
  have hrightCenter : ⁅z, y''⁆ ∈ Subgroup.center Y := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center Y).inv_mem
      (P.commutator_mem_center hrightImage)
  have hcomm : Commute ⁅y', y''⁆ z :=
    commutator_commutes_of_commutators_mem_center hleftCenter hrightCenter
  let c : Y := y * ⁅y', y''⁆⁻¹
  have hcKer : c ∈ P.projection.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [c]
    rw [map_mul, map_inv, map_commutatorElement, hy, hy', hy'',
      SteinbergGroup.x_commutator i t j (Ne.symm hti) htj hij]
    simp
  have hcCenter : c ∈ Subgroup.center Y := P.ker_le_center hcKer
  have hcy : c * ⁅y', y''⁆ = y := by
    dsimp [c]
    group
  rw [← hcy]
  have hcz : Commute c z := by
    change c * z = z * c
    exact (Subgroup.mem_center_iff.mp hcCenter z).symm
  exact hcz.mul_left hcomm

/-- Rank-`n` form of `lifts_commute_of_spare_index`: for `n ≥ 5`, arbitrary
lifts of every pair of non-addable Steinberg roots commute. -/
theorem fin_lifts_commute
    {n : ℕ} (hn : 5 ≤ n)
    (P : CentralExtension Y (SteinbergGroup (Fin n) R))
    (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (r s : R) (y z : Y)
    (hy : P.projection y = SteinbergGroup.x i j hij r)
    (hz : P.projection z = SteinbergGroup.x k l hkl s) :
    Commute y z := by
  obtain ⟨t, hti, htj, htk, htl⟩ := fin_exists_spare_index hn i j k l
  exact lifts_commute_of_spare_index P i j k l t hij hkl hjk hli
    hti htj htk htl r s y z hy hz

end KervaireSteinberg
end NonsoficGroupsExist
