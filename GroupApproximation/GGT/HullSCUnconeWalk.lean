import GroupApproximation.GGT.HullSCUnconeLemmaA
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 8: walking toward a set of points

Three facts used by the walk along a short geodesic of `J` in `GGT/HullSCUnconeLemmaB.lean`:

* `exists_near_of_walk` — if a walk ends in a set `P`, and at each step the current point is within
  `K₁` of `P` or within `K₂` of the next point, its first point is within `K₁ + K₂ L` of `P`;
* `wordDist_le_of_mem_relBall_inr` — two points whose connector lies in a relative ball of a cyclic
  member are close in the un-coned metric;
* `wordDist_vertex_succ_le_one_of_not_inr` — a letter of `J` that is not a letter of a cyclic member
  is a letter of the un-coned alphabet.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u v w

namespace Uncone

section Walk

variable {Q : Type u} [Group Q]

/-- **Walking toward a set.** -/
theorem exists_near_of_walk {S : Set Q} (hS : IsSymmetricGeneratingSet S) (P : Set Q)
    (v : ℕ → Q) (L K₁ K₂ : ℕ) (hend : ∃ p ∈ P, wordDist S (v L) p ≤ K₁)
    (hstep : ∀ j < L,
      (∃ p ∈ P, wordDist S (v j) p ≤ K₁) ∨ wordDist S (v j) (v (j + 1)) ≤ K₂) :
    ∃ p ∈ P, wordDist S (v 0) p ≤ K₁ + K₂ * L := by
  have key : ∀ m : ℕ, m ≤ L → ∃ p ∈ P, wordDist S (v (L - m)) p ≤ K₁ + K₂ * m := by
    intro m
    induction m with
    | zero =>
        intro _
        obtain ⟨p, hp, hd⟩ := hend
        exact ⟨p, hp, by simpa using hd⟩
    | succ m ih =>
        intro hm
        obtain ⟨p, hp, hd⟩ := ih (by omega)
        have hmul : K₂ * (m + 1) = K₂ * m + K₂ := Nat.mul_succ K₂ m
        rcases hstep (L - (m + 1)) (by omega) with ⟨p', hp', hd'⟩ | hd'
        · exact ⟨p', hp', by omega⟩
        · have hj : L - (m + 1) + 1 = L - m := by omega
          rw [hj] at hd'
          have htri := wordDist_triangle hS (v (L - (m + 1))) (v (L - m)) p
          exact ⟨p, hp, by omega⟩
  simpa using key L le_rfl

end Walk

section Removed

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-- **A connector in a relative ball of a cyclic member is short in the un-coned metric.** -/
theorem wordDist_le_of_mem_relBall_inr (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) {T n : ℕ}
    (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) n → (expo g i e).natAbs ≤ T)
    (i : I) {A B : Q} (h : A⁻¹ * B ∈ J.relBall (Sum.inr i) n) :
    wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier A B ≤ T := by
  have hfam : A⁻¹ * B ∈ Subgroup.zpowers (g i) := by
    rw [← hg i]
    exact h.1
  have hS := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hgi : g i ∈ (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier :=
    Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, Or.inl rfl⟩))
  have hb := hT i _ h
  unfold wordDist
  rw [← expo_spec g i hfam]
  exact le_trans (wordNorm_zpow_le hS hgi _) hb

/-- **A letter of `J` outside the cyclic members is a letter of the un-coned alphabet.** -/
theorem wordDist_vertex_succ_le_one_of_not_inr (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) {f : Q} {w : List (RelLetter Q (Sum Lambda I))}
    (hlet : ∀ a ∈ w, J.IsLetter a) {j : ℕ} (hj : j < w.length)
    (hnot : ∀ (i : I) (e : Q), w[j]'hj ≠ RelLetter.comp (Sum.inr i) e) :
    wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (vertex f w j) (vertex f w (j + 1)) ≤ 1 := by
  have hl := hlet _ (List.getElem_mem hj)
  have hval : (w[j]'hj).val ∈ (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier := by
    revert hnot hl
    generalize w[j]'hj = a
    intro hnot hl
    cases a with
    | base b => exact Or.inl (Or.inl hl)
    | comp mu h =>
        cases mu with
        | inl lam => exact Or.inr (Set.mem_iUnion.mpr ⟨lam, hl⟩)
        | inr i => exact absurd rfl (hnot i h)
  unfold wordDist
  rw [vertex_succ w f j hj, inv_mul_cancel_left]
  exact wordNorm_le_one_of_mem hval

end Removed

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.exists_near_of_walk
#audit_axioms GroupApproximation.GGT.Uncone.wordDist_le_of_mem_relBall_inr
#audit_axioms GroupApproximation.GGT.Uncone.wordDist_vertex_succ_le_one_of_not_inr
