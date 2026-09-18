import GroupApproximation.Kourovka1759.Box

/-!
# Swaps of disjoint boxes, and transport into a box

`swap A B h` exchanges two disjoint boxes by their canonical maps; every class transposition
is such a swap. `transHom N` conjugates a permutation of `ℤ` into the box `N` by the canonical
map `ℤ → N` and extends it by the identity; it sends swaps to swaps, hence `CT(ℤ)` into itself.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

open Classical in
/-- The underlying function of the swap of two boxes. -/
noncomputable def swapFun (A B : Box) (n : ℤ) : ℤ :=
  if A.Mem n then B.r + n / A.m * B.m else if B.Mem n then A.r + n / B.m * A.m else n

theorem swapFun_invol {A B : Box} (h : A.Disj B) : Function.Involutive (swapFun A B) := by
  intro n
  by_cases hA : A.Mem n
  · have hB' : B.Mem (B.r + n / A.m * B.m) := B.elt_mem _
    have hA' : ¬ A.Mem (B.r + n / A.m * B.m) := fun h' => h _ h' hB'
    have e1 : swapFun A B n = B.r + n / A.m * B.m := by rw [swapFun, if_pos hA]
    rw [e1, swapFun, if_neg hA', if_pos hB', B.elt_div]
    exact A.eq_of_mem hA
  · by_cases hB : B.Mem n
    · have hA' : A.Mem (A.r + n / B.m * A.m) := A.elt_mem _
      have e1 : swapFun A B n = A.r + n / B.m * A.m := by rw [swapFun, if_neg hA, if_pos hB]
      rw [e1, swapFun, if_pos hA', A.elt_div]
      exact B.eq_of_mem hB
    · have e1 : swapFun A B n = n := by rw [swapFun, if_neg hA, if_neg hB]
      rw [e1, e1]

/-- The swap of two disjoint boxes. -/
noncomputable def swap (A B : Box) (h : A.Disj B) : Perm ℤ := (swapFun_invol h).toPerm _

theorem swap_apply {A B : Box} (h : A.Disj B) (n : ℤ) : swap A B h n = swapFun A B n := rfl

theorem swap_canon {A B : Box} (h : A.Disj B) : CanonOn (swap A B h) A B := fun t => by
  rw [swap_apply, swapFun, if_pos (A.elt_mem t), A.elt_div]

theorem swap_canon' {A B : Box} (h : A.Disj B) : CanonOn (swap A B h) B A := fun t => by
  have : ¬ A.Mem (B.r + t * B.m) := fun h' => h _ h' (B.elt_mem t)
  rw [swap_apply, swapFun, if_neg this, if_pos (B.elt_mem t), B.elt_div]

theorem swap_fix {A B : Box} (h : A.Disj B) {n : ℤ} (hA : ¬ A.Mem n) (hB : ¬ B.Mem n) :
    swap A B h n = n := by
  rw [swap_apply, swapFun, if_neg hA, if_neg hB]

theorem swap_canon_of_disj {A B : Box} (h : A.Disj B) {E : Box} (hA : E.Disj A)
    (hB : E.Disj B) : CanonOn (swap A B h) E E :=
  CanonOn.of_fix fun n hn => swap_fix h (fun ha => hA n hn ha) (fun hb => hB n hn hb)

theorem isClassTransposition_swap {A B : Box} (h : A.Disj B) :
    IsClassTransposition (swap A B h) := by
  refine ⟨A.r, A.m, B.r, B.m, A.hr, A.hrm, B.hr, B.hrm, ?_, ?_, ?_⟩
  · intro t₁ t₂ he
    exact h _ (A.elt_mem t₁) (by rw [he]; exact B.elt_mem t₂)
  · intro t; exact ⟨swap_canon h t, swap_canon' h t⟩
  · intro n h1 h2
    apply swap_fix h
    · intro hA; obtain ⟨t, ht⟩ := (A.mem_iff n).1 hA; exact h1 t ht
    · intro hB; obtain ⟨t, ht⟩ := (B.mem_iff n).1 hB; exact h2 t ht

theorem swap_mem_ct {A B : Box} (h : A.Disj B) : swap A B h ∈ classTranspositionGroup :=
  Subgroup.subset_closure (isClassTransposition_swap h)

/-- Every class transposition is the swap of two disjoint boxes. -/
theorem IsClassTransposition.eq_swap {g : Perm ℤ} (hg : IsClassTransposition g) :
    ∃ (A B : Box) (h : A.Disj B), g = swap A B h := by
  obtain ⟨r₁, m₁, r₂, m₂, h1, h2, h3, h4, hd, hmap, hfix⟩ := hg
  let A : Box := ⟨r₁, m₁, h1, h2⟩
  let B : Box := ⟨r₂, m₂, h3, h4⟩
  have hAB : A.Disj B := by
    intro n ha hb
    obtain ⟨t₁, rfl⟩ := (A.mem_iff n).1 ha
    obtain ⟨t₂, ht₂⟩ := (B.mem_iff _).1 hb
    exact hd t₁ t₂ ht₂
  refine ⟨A, B, hAB, Equiv.ext fun n => ?_⟩
  by_cases ha : A.Mem n
  · obtain ⟨t, rfl⟩ := (A.mem_iff n).1 ha
    rw [(hmap t).1]; exact ((swap_canon hAB) t).symm
  · by_cases hb : B.Mem n
    · obtain ⟨t, rfl⟩ := (B.mem_iff n).1 hb
      rw [(hmap t).2]; exact ((swap_canon' hAB) t).symm
    · rw [swap_fix hAB ha hb]
      apply hfix
      · intro t ht; exact ha (by rw [ht]; exact A.elt_mem t)
      · intro t ht; exact hb (by rw [ht]; exact B.elt_mem t)

/-! ### Transport into a box -/

open Classical in
/-- The function underlying `transHom N g`. -/
noncomputable def transFun (N : Box) (g : Perm ℤ) (n : ℤ) : ℤ :=
  if N.Mem n then N.r + g (n / N.m) * N.m else n

theorem transFun_pos (N : Box) (g : Perm ℤ) {n : ℤ} (hn : N.Mem n) :
    transFun N g n = N.r + g (n / N.m) * N.m := by
  rw [transFun, if_pos hn]

theorem transFun_neg (N : Box) (g : Perm ℤ) {n : ℤ} (hn : ¬ N.Mem n) : transFun N g n = n := by
  rw [transFun, if_neg hn]

theorem transFun_left (N : Box) (g : Perm ℤ) :
    Function.LeftInverse (transFun N g⁻¹) (transFun N g) := by
  intro n
  by_cases hn : N.Mem n
  · rw [transFun_pos N g hn, transFun_pos N _ (N.elt_mem _), N.elt_div]
    simp only [Perm.coe_inv, Equiv.symm_apply_apply]
    exact N.eq_of_mem hn
  · rw [transFun_neg N g hn, transFun_neg N _ hn]

theorem transFun_mul (N : Box) (g h : Perm ℤ) (n : ℤ) :
    transFun N (g * h) n = transFun N g (transFun N h n) := by
  by_cases hn : N.Mem n
  · rw [transFun_pos N _ hn, transFun_pos N h hn, transFun_pos N g (N.elt_mem _), N.elt_div,
      Perm.mul_apply]
  · rw [transFun_neg N _ hn, transFun_neg N h hn, transFun_neg N g hn]

/-- Transport of a permutation into the box `N`, as a permutation of `ℤ`. -/
noncomputable def transPerm (N : Box) (g : Perm ℤ) : Perm ℤ where
  toFun := transFun N g
  invFun := transFun N g⁻¹
  left_inv := transFun_left N g
  right_inv := by have := transFun_left N g⁻¹; rwa [inv_inv] at this

/-- Transport into `N` as a group homomorphism. -/
noncomputable def transHom (N : Box) : Perm ℤ →* Perm ℤ where
  toFun := transPerm N
  map_one' := Equiv.ext fun n => by
    show transFun N 1 n = n
    by_cases hn : N.Mem n
    · rw [transFun, if_pos hn]; exact N.eq_of_mem hn
    · rw [transFun, if_neg hn]
  map_mul' g h := Equiv.ext fun n => transFun_mul N g h n

theorem transHom_apply (N : Box) (g : Perm ℤ) (n : ℤ) : transHom N g n = transFun N g n := rfl

theorem transHom_fix (N : Box) (g : Perm ℤ) {n : ℤ} (hn : ¬ N.Mem n) : transHom N g n = n := by
  rw [transHom_apply, transFun, if_neg hn]

theorem transHom_canon (N : Box) {g : Perm ℤ} {A B : Box} (hg : CanonOn g A B) :
    CanonOn (transHom N g) (place N A) (place N B) := fun t => by
  rw [transHom_apply, place_elt, transFun_pos N g (N.elt_mem _), N.elt_div, hg t, place_elt]

theorem transHom_swap (N : Box) {A B : Box} (h : A.Disj B) :
    transHom N (swap A B h) = swap (place N A) (place N B) (disj_place h) := by
  refine Equiv.ext fun n => ?_
  by_cases ha : (place N A).Mem n
  · exact (transHom_canon N (swap_canon h)).agree (swap_canon (disj_place h)) ha
  by_cases hb : (place N B).Mem n
  · exact (transHom_canon N (swap_canon' h)).agree (swap_canon' (disj_place h)) hb
  rw [swap_fix _ ha hb]
  by_cases hn : N.Mem n
  · have ha' : ¬ A.Mem (n / N.m) := fun h' => ha (mem_place.2 ⟨hn, h'⟩)
    have hb' : ¬ B.Mem (n / N.m) := fun h' => hb (mem_place.2 ⟨hn, h'⟩)
    rw [transHom_apply, transFun_pos N _ hn, swap_fix h ha' hb']
    exact N.eq_of_mem hn
  · exact transHom_fix N _ hn

theorem transHom_mem_ct (N : Box) {g : Perm ℤ} (hg : g ∈ classTranspositionGroup) :
    transHom N g ∈ classTranspositionGroup := by
  have hle : classTranspositionGroup ≤ classTranspositionGroup.comap (transHom N) := by
    rw [classTranspositionGroup, Subgroup.closure_le]
    intro x hx
    obtain ⟨A, B, h, rfl⟩ := IsClassTransposition.eq_swap hx
    show transHom N (swap A B h) ∈ classTranspositionGroup
    rw [transHom_swap]
    exact swap_mem_ct _
  exact hle hg

end GroupApproximation.Kourovka1759
