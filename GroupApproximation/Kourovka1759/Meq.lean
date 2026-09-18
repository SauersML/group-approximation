import GroupApproximation.Kourovka1759.Tree

/-!
# Equivalence of multisets of boxes

`MEq C D`: some element of `CT(ℤ)` maps the boxes of `C` canonically onto the boxes of `D`.
This is `Equi` with the order of the boxes forgotten. It turns the list bookkeeping of the
exchange and replacement moves into additive arithmetic of multisets. We also record the
transport of a refinement along an equivalence (`MEq.graft`) and the leaves of a tree as a
multiset.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

instance : DecidableEq Box := fun A B => decidable_of_iff _ Box.ext_iff.symm

namespace Box

theorem disj_place_right {N N' : Box} (h : N.Disj N') (Y : Box) : N.Disj (place N' Y) :=
  fun n hn hy => h n hn (place_mem_of hy)

theorem disj_place_left {N N' : Box} (h : N.Disj N') (X : Box) : (place N X).Disj N' :=
  fun n hx hn => h n (place_mem_of hx) hn

theorem mem_r (A : Box) : A.Mem A.r := by
  have := A.elt_mem 0
  rwa [zero_mul, add_zero] at this

theorem ne_of_disj {A B : Box} (h : A.Disj B) : A ≠ B := by
  rintro rfl
  exact h _ A.mem_r A.mem_r

/-- Two boxes with the same modulus and a common point are equal. -/
theorem eq_of_mem_of_m {A B : Box} {n : ℤ} (hA : A.Mem n) (hB : B.Mem n) (hm : A.m = B.m) :
    A = B := by
  unfold Mem at hA hB
  ext
  · rw [← hA, ← hB, hm]
  · exact hm

/-- A box of modulus `q` is a child of the `q`-split of `ℤ`. -/
theorem eq_child {Y : Box} {q : ℕ} (h : Y.m = q) : ∃ j : Fin q, Y = child q j := by
  have h1 := Y.hr
  have h2 := Y.hrm
  have h3 : ((Y.r.toNat : ℕ) : ℤ) = Y.r := Int.toNat_of_nonneg h1
  refine ⟨⟨Y.r.toNat, by omega⟩, ?_⟩
  ext
  · show Y.r = ((Y.r.toNat : ℕ) : ℤ)
    exact h3.symm
  · show Y.m = ((q : ℕ) : ℤ)
    exact h

end Box

theorem map_place_place (E X : Box) (S : Multiset Box) :
    (S.map (place X)).map (place E) = S.map (place (place E X)) := by
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun Y _ => place_assoc E X Y

theorem map_fsum {ι : Type*} (s : Finset ι) (f : Box → Box) (g : ι → Multiset Box) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, ih]

/-- Some element of `CT(ℤ)` maps the boxes of `C` canonically onto the boxes of `D`. -/
def MEq (C D : Multiset Box) : Prop :=
  ∃ h ∈ classTranspositionGroup, ∃ c d : List Box, (c : Multiset Box) = C ∧
    (d : Multiset Box) = D ∧ List.Forall₂ (CanonOn h) c d

theorem erase_mid (l₁ l₂ : List Box) (a : Box) :
    ((l₁ ++ a :: l₂ : List Box) : Multiset Box).erase a = ((l₁ ++ l₂ : List Box) : Multiset Box) := by
  rw [Multiset.coe_eq_coe.2 List.perm_middle, ← Multiset.cons_coe, Multiset.erase_cons_head]

theorem forall₂_split {R : Box → Box → Prop} {p q : List Box} (h : List.Forall₂ R p q) :
    ∀ {E : Box}, E ∈ p → ∃ E' p₁ p₂ q₁ q₂, p = p₁ ++ E :: p₂ ∧ q = q₁ ++ E' :: q₂ ∧ R E E' ∧
      List.Forall₂ R (p₁ ++ p₂) (q₁ ++ q₂) := by
  induction h with
  | nil => intro E hE; simp at hE
  | @cons a b p q hab hpq ih =>
    intro E hE
    rcases List.mem_cons.1 hE with rfl | hE
    · exact ⟨b, [], p, [], q, rfl, rfl, hab, hpq⟩
    · obtain ⟨E', p₁, p₂, q₁, q₂, rfl, rfl, hR, hf⟩ := ih hE
      exact ⟨E', a :: p₁, p₂, b :: q₁, q₂, rfl, rfl, hR, .cons hab hf⟩

namespace MEq

theorem of_equi {c d : List Box} (h : Equi c d) : MEq c d := by
  obtain ⟨g, hg, d', hp, hf⟩ := h
  exact ⟨g, hg, c, d', rfl, Multiset.coe_eq_coe.2 hp, hf⟩

theorem to_equi {c d : List Box} (h : MEq c d) : Equi c d := by
  obtain ⟨g, hg, c₁, d₁, hc, hd, hf⟩ := h
  obtain ⟨w, hw, hwp⟩ := List.perm_comp_forall₂ (Multiset.coe_eq_coe.1 hc).symm hf
  exact ⟨g, hg, w, hwp.trans (Multiset.coe_eq_coe.1 hd), hw⟩

theorem refl (C : Multiset Box) : MEq C C :=
  ⟨1, one_mem _, C.toList, C.toList, Multiset.coe_toList C, Multiset.coe_toList C,
    forall₂_canon_one _⟩

theorem of_eq {C D : Multiset Box} (h : C = D) : MEq C D := by
  subst h
  exact refl _

theorem symm {C D : Multiset Box} (h : MEq C D) : MEq D C := by
  obtain ⟨g, hg, c, d, hc, hd, hf⟩ := h
  exact ⟨g⁻¹, inv_mem hg, d, c, hd, hc, forall₂_canon_inv hf⟩

theorem trans {C D E : Multiset Box} (h₁ : MEq C D) (h₂ : MEq D E) : MEq C E := by
  obtain ⟨g, hg, c, d, hc, hd, hf⟩ := h₁
  obtain ⟨g', hg', d', e, hd', he, hf'⟩ := h₂
  obtain ⟨w, hw, hwp⟩ :=
    List.perm_comp_forall₂ (Multiset.coe_eq_coe.1 (hd.trans hd'.symm)) hf'
  exact ⟨g' * g, mul_mem hg' hg, c, w, hc, (Multiset.coe_eq_coe.2 hwp).trans he,
    forall₂_canon_comp hf hw⟩

theorem card_eq {C D : Multiset Box} (h : MEq C D) : Multiset.card C = Multiset.card D := by
  obtain ⟨g, -, c, d, rfl, rfl, hf⟩ := h
  simp only [Multiset.coe_card]
  exact hf.length_eq

/-- **Graft.** An equivalence maps a box `E` of `P` canonically onto a box `E'` of `Q`, so
refining `E` and `E'` by the same multiset keeps the two sides equivalent. -/
theorem graft {P Q : Multiset Box} (h : MEq P Q) {E : Box} (hE : E ∈ P) :
    ∃ E' ∈ Q, ∀ u : Multiset Box,
      MEq (P.erase E + u.map (place E)) (Q.erase E' + u.map (place E')) := by
  obtain ⟨g, hg, p, q, rfl, rfl, hf⟩ := h
  obtain ⟨E', p₁, p₂, q₁, q₂, rfl, rfl, hR, hf'⟩ := forall₂_split hf (Multiset.mem_coe.1 hE)
  refine ⟨E', Multiset.mem_coe.2 (List.mem_append.2 (Or.inr List.mem_cons_self)), fun u => ?_⟩
  refine ⟨g, hg, p₁ ++ p₂ ++ u.toList.map (place E), q₁ ++ q₂ ++ u.toList.map (place E'), ?_, ?_,
    List.rel_append hf' (forall₂_canon_map hR u.toList)⟩
  · rw [erase_mid]
    simp only [← Multiset.coe_add, ← Multiset.map_coe, Multiset.coe_toList]
  · rw [erase_mid]
    simp only [← Multiset.coe_add, ← Multiset.map_coe, Multiset.coe_toList]

/-- **Exchange.** Swapping the contents of two disjoint boxes. -/
theorem exchange {A B : Box} (hAB : A.Disj B) (C₀ u v : Multiset Box)
    (hC₀ : ∀ E ∈ C₀, E.Disj A ∧ E.Disj B) :
    MEq (C₀ + u.map (place A) + v.map (place B)) (C₀ + u.map (place B) + v.map (place A)) := by
  have h := of_equi (Equi.exchange hAB C₀.toList u.toList v.toList
    (fun E hE => hC₀ E (Multiset.mem_toList.1 hE)))
  simpa only [← Multiset.coe_add, ← Multiset.map_coe, Multiset.coe_toList] using h

/-- **Replacement.** Replacing the contents of one box by an equivalent multiset. -/
theorem local_box {N : Box} {C₀ u v : Multiset Box} (hC₀ : ∀ E ∈ C₀, E.Disj N)
    (huv : MEq u v) : MEq (C₀ + u.map (place N)) (C₀ + v.map (place N)) := by
  obtain ⟨g, hg, c, d, rfl, rfl, hf⟩ := huv
  have h := of_equi (Equi.local_box (C₀ := C₀.toList)
    (fun E hE => hC₀ E (Multiset.mem_toList.1 hE)) (⟨g, hg, d, List.Perm.refl d, hf⟩ : Equi c d))
  simpa only [← Multiset.coe_add, ← Multiset.map_coe, Multiset.coe_toList] using h

end MEq

/-- The boxes of `S` are pairwise disjoint. -/
def PD (S : Multiset Box) : Prop := ∀ x ∈ S, ∀ y ∈ S.erase x, x.Disj y

theorem pd_coe {l : List Box} (h : l.Pairwise Box.Disj) : PD (l : Multiset Box) := by
  intro x hx y hy
  rw [Multiset.coe_erase] at hy
  have hp := ((List.perm_cons_erase (Multiset.mem_coe.1 hx)).pairwise_iff
    (fun h => h.symm)).1 h
  exact (List.pairwise_cons.1 hp).1 y (Multiset.mem_coe.1 hy)

theorem PD.nodup {S : Multiset Box} (h : PD S) : S.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro x
  by_contra hx
  push_neg at hx
  have h1 : x ∈ S := Multiset.count_pos.1 (by omega)
  have h2 : x ∈ S.erase x := Multiset.count_pos.1 (by rw [Multiset.count_erase_self]; omega)
  exact h x h1 x h2 _ x.mem_r x.mem_r

namespace STree

/-- The leaves of a tree, as a multiset. -/
def ml (t : STree) : Multiset Box := t.leaves

theorem coe_flatMap {α β : Type*} (l : List α) (f : α → List β) :
    ((l.flatMap f : List β) : Multiset β) = (l.map fun a => ((f a : List β) : Multiset β)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

theorem ml_leaf : ml leaf = {univ} := by simp [ml, leaves]

theorem ml_node (k : ℕ) (c : Fin k → STree) :
    ml (node k c) = ∑ j, (ml (c j)).map (place (child k j)) := by
  rw [Fin.sum_univ_def]
  simp only [ml, leaves, coe_flatMap, Multiset.map_coe]

theorem pd_ml (t : STree) : PD (ml t) := pd_coe (pairwise t)

theorem cover_ml {t : STree} (ht : WF t) (n : ℤ) : ∃ B ∈ ml t, B.Mem n := by
  obtain ⟨B, hB, h⟩ := cover t ht n
  exact ⟨B, Multiset.mem_coe.2 hB, h⟩

theorem teq_iff {s t : STree} : TEq s t ↔ MEq (ml s) (ml t) := ⟨MEq.of_equi, MEq.to_equi⟩

end STree

end GroupApproximation.Kourovka1759
