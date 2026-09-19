import GroupApproximation.Kourovka1759.PC

/-!
# Equivalence of box lists

`Equi C D`: some element of `CT(ℤ)` maps the boxes of `C` canonically onto the boxes of `D`, in
some order. We prove it is an equivalence relation, that swapping the contents of two disjoint
boxes and replacing the contents of one box by an equivalent list preserve it, that any
reordering of pairwise disjoint boxes is realized in `CT(ℤ)`, and that a common refinement cancels.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box

/-- Some element of `CT(ℤ)` maps the boxes of `C` canonically onto those of `D`, in some order. -/
def Equi (C D : List Box) : Prop :=
  ∃ h ∈ classTranspositionGroup, ∃ D' : List Box, D'.Perm D ∧ List.Forall₂ (CanonOn h) C D'

theorem forall₂_canon_one (C : List Box) : List.Forall₂ (CanonOn 1) C C :=
  List.forall₂_same.2 fun x _ => CanonOn.one x

theorem forall₂_canon_comp {g h : Perm ℤ} {C D E : List Box}
    (h1 : List.Forall₂ (CanonOn g) C D) (h2 : List.Forall₂ (CanonOn h) D E) :
    List.Forall₂ (CanonOn (h * g)) C E := by
  induction h1 generalizing E with
  | nil => cases h2; exact .nil
  | cons ha _ ih => cases h2 with | cons hb h2' => exact .cons (ha.comp hb) (ih h2')

theorem forall₂_canon_inv {g : Perm ℤ} {C D : List Box} (h1 : List.Forall₂ (CanonOn g) C D) :
    List.Forall₂ (CanonOn g⁻¹) D C := by
  induction h1 with
  | nil => exact .nil
  | cons ha _ ih => exact .cons ha.inv ih

theorem forall₂_canon_map {g : Perm ℤ} {A B : Box} (hg : CanonOn g A B) (u : List Box) :
    List.Forall₂ (CanonOn g) (u.map (place A)) (u.map (place B)) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun X _ => hg.place X

theorem forall₂_diag {α : Type*} {S : α → α → Prop} {l : List α} (h : List.Forall₂ S l l) :
    ∀ X ∈ l, S X X := by
  induction l with
  | nil => intro X hX; simp at hX
  | cons a l ih =>
    cases h with
    | cons hab h' =>
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hab
      · exact ih h' X hX

namespace Equi

theorem of_perm {C D : List Box} (h : C.Perm D) : Equi C D :=
  ⟨1, one_mem _, C, h, forall₂_canon_one C⟩

theorem refl (C : List Box) : Equi C C := of_perm (List.Perm.refl C)

theorem symm {C D : List Box} (h : Equi C D) : Equi D C := by
  obtain ⟨g, hg, D', hp, hf⟩ := h
  obtain ⟨w, hw, hwp⟩ := List.perm_comp_forall₂ hp.symm (forall₂_canon_inv hf)
  exact ⟨g⁻¹, inv_mem hg, w, hwp, hw⟩

theorem trans {C D E : List Box} (h₁ : Equi C D) (h₂ : Equi D E) : Equi C E := by
  obtain ⟨g, hg, D₁, p₁, f₁⟩ := h₁
  obtain ⟨h, hh, E₁, p₂, f₂⟩ := h₂
  obtain ⟨w, hw, hwp⟩ := List.perm_comp_forall₂ p₁ f₂
  exact ⟨h * g, mul_mem hh hg, w, hwp.trans p₂, forall₂_canon_comp f₁ hw⟩

theorem perm_left {C C' D : List Box} (hp : C.Perm C') (h : Equi C D) : Equi C' D :=
  (of_perm hp.symm).trans h

theorem perm_right {C D D' : List Box} (hp : D.Perm D') (h : Equi C D) : Equi C D' :=
  h.trans (of_perm hp)

/-- Swapping the contents of two disjoint boxes. -/
theorem exchange {A B : Box} (hAB : A.Disj B) (C₀ u v : List Box)
    (hC₀ : ∀ E ∈ C₀, E.Disj A ∧ E.Disj B) :
    Equi (C₀ ++ u.map (place A) ++ v.map (place B))
      (C₀ ++ u.map (place B) ++ v.map (place A)) := by
  refine ⟨swap A B hAB, swap_mem_ct hAB, _, List.Perm.refl _, ?_⟩
  refine List.rel_append (List.rel_append ?_ (forall₂_canon_map (swap_canon hAB) u))
    (forall₂_canon_map (swap_canon' hAB) v)
  exact List.forall₂_same.2 fun E hE => swap_canon_of_disj hAB (hC₀ E hE).1 (hC₀ E hE).2

/-- Replacing the contents of one box by an equivalent list. -/
theorem local_box {N : Box} {C₀ u v : List Box} (hC₀ : ∀ E ∈ C₀, E.Disj N) (huv : Equi u v) :
    Equi (C₀ ++ u.map (place N)) (C₀ ++ v.map (place N)) := by
  obtain ⟨h, hh, v', hp, hf⟩ := huv
  refine ⟨transHom N h, transHom_mem_ct N hh, C₀ ++ v'.map (place N),
    (hp.map _).append_left C₀, List.rel_append ?_ ?_⟩
  · exact List.forall₂_same.2 fun E hE =>
      CanonOn.of_fix fun n hn => transHom_fix N h (fun hN => hC₀ E hE n hn hN)
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hf.imp fun X Y hXY => transHom_canon N hXY

end Equi

/-- Any reordering of pairwise disjoint boxes is realized canonically by an element of `CT(ℤ)`
that fixes every point outside the boxes. -/
theorem sym_perm {D D' : List Box} (hp : D.Perm D') (hd : D.Pairwise Box.Disj) :
    ∃ σ ∈ classTranspositionGroup, List.Forall₂ (CanonOn σ) D D' ∧
      ∀ n, (∀ B ∈ D, ¬ B.Mem n) → σ n = n := by
  induction hp with
  | nil => exact ⟨1, one_mem _, .nil, fun _ _ => rfl⟩
  | cons x _ ih =>
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 hd
    obtain ⟨σ, hσ, hf, hfix⟩ := ih hl
    refine ⟨σ, hσ, .cons (CanonOn.of_fix fun n hn => hfix n fun B hB hBn => hx B hB n hn hBn) hf,
      fun n hn => hfix n fun B hB => hn B (List.mem_cons_of_mem _ hB)⟩
  | swap x y l =>
    obtain ⟨hy, hxl⟩ := List.pairwise_cons.1 hd
    obtain ⟨hx, _⟩ := List.pairwise_cons.1 hxl
    have hyx : y.Disj x := hy x (List.mem_cons_self)
    refine ⟨swap y x hyx, swap_mem_ct hyx, .cons (swap_canon hyx) (.cons (swap_canon' hyx) ?_),
      fun n hn => swap_fix hyx (hn y List.mem_cons_self)
        (hn x (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    exact List.forall₂_same.2 fun E hE => swap_canon_of_disj hyx
      (hy E (List.mem_cons_of_mem _ hE)).symm (hx E hE).symm
  | trans p₁ _ ih₁ ih₂ =>
    obtain ⟨σ₁, h₁, f₁, x₁⟩ := ih₁ hd
    obtain ⟨σ₂, h₂, f₂, x₂⟩ := ih₂ ((p₁.pairwise_iff (fun h => h.symm)).1 hd)
    refine ⟨σ₂ * σ₁, mul_mem h₂ h₁, forall₂_canon_comp f₁ f₂, fun n hn => ?_⟩
    rw [Perm.mul_apply, x₁ n hn]
    exact x₂ n fun B hB => hn B (p₁.mem_iff.2 hB)

theorem forall₂_flatMap_split {R : Box → Box → Prop} {x : List Box} {F G : Box → Box → Box} :
    ∀ {u v : List Box}, u.length = v.length →
      List.Forall₂ R (u.flatMap fun U => x.map (F U)) (v.flatMap fun V => x.map (G V)) →
      List.Forall₂ (fun U V => List.Forall₂ R (x.map (F U)) (x.map (G V))) u v
  | [], [], _, _ => .nil
  | U :: us, V :: vs, hl, h => by
    simp only [List.flatMap_cons] at h
    have hlen : (x.map (F U)).length = (x.map (G V)).length := by simp
    have h1 := List.forall₂_take (x.map (F U)).length h
    have h2 := List.forall₂_drop (x.map (F U)).length h
    rw [List.take_left' rfl, hlen, List.take_left' rfl] at h1
    rw [List.drop_left' rfl, hlen, List.drop_left' rfl] at h2
    exact .cons h1 (forall₂_flatMap_split (by simpa using hl) h2)

/-- **Cancellation**: a common refinement of every box by the partition `x` cancels. -/
theorem Equi.cancel {u v x : List Box} (hx : ∀ n, ∃ X ∈ x, X.Mem n) (hlen : u.length = v.length)
    (hdisj : (v.flatMap fun V => x.map (place V)).Pairwise Box.Disj)
    (h : Equi (u.flatMap fun U => x.map (place U)) (v.flatMap fun V => x.map (place V))) :
    Equi u v := by
  obtain ⟨g, hg, D', hp, hf⟩ := h
  obtain ⟨σ, hσ, hfσ, -⟩ := sym_perm hp ((hp.pairwise_iff (fun h => h.symm)).2 hdisj)
  refine ⟨σ * g, mul_mem hσ hg, v, List.Perm.refl v, ?_⟩
  have hall := forall₂_flatMap_split hlen (forall₂_canon_comp hf hfσ)
  refine hall.imp fun U V hUV => ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hUV
  intro t
  obtain ⟨X, hXx, hX⟩ := hx t
  have hc : CanonOn (σ * g) (place U X) (place V X) := forall₂_diag hUV X hXx
  obtain ⟨s, rfl⟩ := (X.mem_iff t).1 hX
  have := hc s
  rw [place_elt, place_elt] at this
  exact this

end GroupApproximation.Kourovka1759
