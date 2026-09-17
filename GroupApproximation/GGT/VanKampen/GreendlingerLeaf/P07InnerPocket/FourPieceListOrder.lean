import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceListMono
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: the four-piece order of a labelled cyclic list

Lane `gl-p07-10` (`lanes/carto-gl-p07.md`), list layer.  Infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`; certifies no printed sentence on its own.
The mathematical proof of the lane is in `FourPieceOrder.lean`.

## Statement

`exists_fourPiece`.  Let every entry of `l` carry a label `P1`, `P2`, `Pa` or `Pb`, and let the
four derived classes `c₁ = P1`, `c₂ = ¬P1 ∧ P2`, `c₁ ∨ (¬P2 ∧ Pb)`, `c₁ ∨ (¬P2 ∧ ¬Pb)` be
cyclically non-interleaving.  Then a rotation of `l` is `R₁ ++ U₁ ++ R₂ ++ U₂` with `U₁` all `P1`,
`U₂` all `P2`, and either both `R₁`, `R₂` monochrome (`Pa` or `Pb`), or `R₁ ++ R₂` all `Pa ∨ Pb`
and a run empty.

## Proof

1. `c₁` is a cyclic block: some rotation is `U ++ V` (`exists_rotate_block`).  If `U = []`, `c₂` is
   a cyclic block `W ++ Z`; rotate to `Z ++ [] ++ [] ++ W`.
2. Otherwise take `u ∈ U` and split `V = X ++ W ++ Y ++ r` greedily into `¬c₂, c₂, ¬c₂` blocks.
   If `r ≠ []`, the heads of `W`, `Y`, `r` with `u` alternate in `c₂`.
3. If `W = []`, the answer is `[] ++ U ++ (X ++ Y) ++ []`.  Otherwise rotate to `Y ++ U ++ X ++ W`.
   The entries of `X` and `Y` are neither `P1` nor `P2`, so `Pa` or `Pb`.  A pair of an `a`-entry
   (not `Pb`) and a `b`-entry inside `X` or `Y`, together with `u ∈ U` and `w ∈ W`, alternates in the
   `b`-class or the `a`-class; so `mono_or` applies.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece

section Lists

variable {α : Type*}

/-- **The four-piece order of a labelled cyclic list.** -/
theorem exists_fourPiece {P1 P2 Pa Pb : α → Prop} {l : List α}
    (hlab : ∀ x ∈ l, P1 x ∨ P2 x ∨ Pa x ∨ Pb x) (h1 : CyclicNoInterleave P1 l)
    (h2 : CyclicNoInterleave (fun x => ¬ P1 x ∧ P2 x) l)
    (hb : CyclicNoInterleave (fun x => P1 x ∨ (¬ P2 x ∧ Pb x)) l)
    (ha : CyclicNoInterleave (fun x => P1 x ∨ (¬ P2 x ∧ ¬ Pb x)) l) :
    ∃ (n : ℕ) (R₁ U₁ R₂ U₂ : List α), l.rotate n = R₁ ++ U₁ ++ R₂ ++ U₂ ∧
      (∀ x ∈ U₁, P1 x) ∧ (∀ x ∈ U₂, P2 x) ∧
      ((((∀ x ∈ R₁, Pa x) ∨ ∀ x ∈ R₁, Pb x) ∧ ((∀ x ∈ R₂, Pa x) ∨ ∀ x ∈ R₂, Pb x)) ∨
        ((∀ x ∈ R₁ ++ R₂, Pa x ∨ Pb x) ∧ (U₁ = [] ∨ U₂ = []))) := by
  obtain ⟨n₁, U, V, hrot₁, hU, hV⟩ := exists_rotate_block h1
  cases U with
  | nil =>
    obtain ⟨n₂, W, Z, hrot₂, hW, hZ⟩ := exists_rotate_block h2
    refine ⟨n₂ + W.length, Z, [], [], W, ?_, fun _ hx => by simp at hx,
      fun x hx => (hW x hx).2, Or.inr ⟨?_, Or.inl rfl⟩⟩
    · rw [← List.rotate_rotate, hrot₂, List.rotate_append_length_eq]
      simp only [List.append_nil]
    · intro x hx
      rw [List.append_nil] at hx
      have hxl : x ∈ l := mem_of_rotate_eq hrot₂ (List.mem_append.mpr (Or.inr hx))
      have hx₁ : x ∈ l.rotate n₁ := List.mem_rotate.mpr hxl
      rw [hrot₁, List.nil_append] at hx₁
      have hn1 : ¬ P1 x := hV x hx₁
      exact ((hlab x hxl).resolve_left hn1).resolve_left fun hp => hZ x hx ⟨hn1, hp⟩
  | cons u U' =>
    have hu : P1 u := hU u List.mem_cons_self
    have hu2 : ¬ (¬ P1 u ∧ P2 u) := fun h => h.1 hu
    obtain ⟨X, r₁, rfl, hX, hr₁⟩ := exists_prefix_split (fun x => ¬ (¬ P1 x ∧ P2 x)) V
    obtain ⟨W, r₂, rfl, hW, hr₂⟩ := exists_prefix_split (fun x => ¬ P1 x ∧ P2 x) r₁
    obtain ⟨Y, r₃, rfl, hY, hr₃⟩ := exists_prefix_split (fun x => ¬ (¬ P1 x ∧ P2 x)) r₂
    have hside : ∀ x, x ∈ X ++ (W ++ (Y ++ r₃)) → ¬ (¬ P1 x ∧ P2 x) →
        ¬ P1 x ∧ ¬ P2 x ∧ (Pa x ∨ Pb x) := by
      intro x hx hc
      have h₁ : ¬ P1 x := hV x hx
      have h₂ : ¬ P2 x := fun hp => hc ⟨h₁, hp⟩
      have hl : x ∈ l := mem_of_rotate_eq hrot₁ (List.mem_append.mpr (Or.inr hx))
      exact ⟨h₁, h₂, ((hlab x hl).resolve_left h₁).resolve_left h₂⟩
    have hXs : ∀ x ∈ X, ¬ P1 x ∧ ¬ P2 x ∧ (Pa x ∨ Pb x) :=
      fun x hx => hside x (List.mem_append.mpr (Or.inl hx)) (hX x hx)
    have hYs : ∀ x ∈ Y, ¬ P1 x ∧ ¬ P2 x ∧ (Pa x ∨ Pb x) := fun x hx => hside x
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inl hx)))))) (hY x hx)
    cases r₃ with
    | cons y s =>
      exfalso
      obtain ⟨y₀, hy₀⟩ := exists_mem_of_heads (B := fun x => ¬ (¬ P1 x ∧ P2 x))
        (C := fun x => ¬ ¬ (¬ P1 x ∧ P2 x)) (fun _ b c => c b) hr₂ hr₃ (List.cons_ne_nil y s)
      obtain ⟨w₀, hw₀⟩ := exists_mem_of_heads (B := fun x => ¬ ¬ (¬ P1 x ∧ P2 x))
        (C := fun x => ¬ (¬ P1 x ∧ P2 x)) (fun _ b c => b c) hr₁ hr₂ (by simp)
      have hs : [u, w₀, y₀, y] <+ (u :: U') ++ (X ++ (W ++ (Y ++ y :: s))) :=
        sublist_four_skip List.mem_cons_self hw₀ hy₀ List.mem_cons_self
      exact h2.not_baba hrot₁ u w₀ y₀ y hs hu2 (hW w₀ hw₀) (hY y₀ hy₀)
        (Classical.not_not.mp (hr₃ y s rfl))
    | nil =>
      cases W with
      | nil =>
        refine ⟨n₁, [], u :: U', X ++ Y, [], ?_, hU, fun _ hx => by simp at hx,
          Or.inr ⟨?_, Or.inr rfl⟩⟩
        · rw [hrot₁]
          simp only [List.nil_append, List.append_nil]
        · intro x hx
          rw [List.nil_append] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact (hXs x hx).2.2
          · exact (hYs x hx).2.2
      | cons w₀ W' =>
        have hw : ¬ P1 w₀ ∧ P2 w₀ := hW w₀ List.mem_cons_self
        have hwa : ¬ (P1 w₀ ∨ (¬ P2 w₀ ∧ ¬ Pb w₀)) := fun h => h.elim hw.1 fun h' => h'.1 hw.2
        have hwb : ¬ (P1 w₀ ∨ (¬ P2 w₀ ∧ Pb w₀)) := fun h => h.elim hw.1 fun h' => h'.1 hw.2
        refine ⟨n₁ + ((u :: U') ++ X ++ (w₀ :: W')).length, Y, u :: U', X, w₀ :: W', ?_, hU,
          fun x hx => (hW x hx).2, Or.inl ⟨?_, ?_⟩⟩
        · rw [← List.rotate_rotate, hrot₁]
          have e : (u :: U') ++ (X ++ ((w₀ :: W') ++ (Y ++ []))) =
              ((u :: U') ++ X ++ (w₀ :: W')) ++ Y := by
            simp only [List.append_nil, List.append_assoc]
          rw [e, List.rotate_append_length_eq]
          simp only [List.append_assoc]
        · refine mono_or (fun x hx => (hYs x hx).2.2) ?_ ?_
          · intro x₁ x₂ hp hnb hb₂
            have hx₁ := hYs x₁ (hp.subset (by simp))
            have hx₂ := hYs x₂ (hp.subset (by simp))
            have hs : [u, w₀, x₁, x₂] <+ (u :: U') ++ (X ++ ((w₀ :: W') ++ (Y ++ []))) :=
              (List.singleton_sublist.mpr List.mem_cons_self).append
                (((List.singleton_sublist.mpr List.mem_cons_self).append
                  (hp.trans (List.sublist_append_left Y []))).trans (List.sublist_append_right X _))
            exact ha.not_abab hrot₁ u w₀ x₁ x₂ hs (Or.inl hu) hwa (Or.inr ⟨hx₁.2.1, hnb⟩)
              fun h => h.elim hx₂.1 fun h' => h'.2 hb₂
          · intro x₁ x₂ hp hnb hb₂
            have hx₁ := hYs x₁ (hp.subset (by simp))
            have hx₂ := hYs x₂ (hp.subset (by simp))
            have hs : [u, w₀, x₂, x₁] <+ (u :: U') ++ (X ++ ((w₀ :: W') ++ (Y ++ []))) :=
              (List.singleton_sublist.mpr List.mem_cons_self).append
                (((List.singleton_sublist.mpr List.mem_cons_self).append
                  (hp.trans (List.sublist_append_left Y []))).trans (List.sublist_append_right X _))
            exact hb.not_abab hrot₁ u w₀ x₂ x₁ hs (Or.inl hu) hwb (Or.inr ⟨hx₂.2.1, hb₂⟩)
              fun h => h.elim hx₁.1 fun h' => hnb h'.2
        · refine mono_or (fun x hx => (hXs x hx).2.2) ?_ ?_
          · intro x₁ x₂ hp hnb hb₂
            have hx₁ := hXs x₁ (hp.subset (by simp))
            have hx₂ := hXs x₂ (hp.subset (by simp))
            have hs : [u, x₁, x₂, w₀] <+ (u :: U') ++ (X ++ ((w₀ :: W') ++ (Y ++ []))) :=
              (List.singleton_sublist.mpr List.mem_cons_self).append (hp.append
                (List.singleton_sublist.mpr (List.mem_append.mpr (Or.inl List.mem_cons_self))))
            exact hb.not_abab hrot₁ u x₁ x₂ w₀ hs (Or.inl hu)
              (fun h => h.elim hx₁.1 fun h' => hnb h'.2) (Or.inr ⟨hx₂.2.1, hb₂⟩) hwb
          · intro x₁ x₂ hp hnb hb₂
            have hx₁ := hXs x₁ (hp.subset (by simp))
            have hx₂ := hXs x₂ (hp.subset (by simp))
            have hs : [u, x₂, x₁, w₀] <+ (u :: U') ++ (X ++ ((w₀ :: W') ++ (Y ++ []))) :=
              (List.singleton_sublist.mpr List.mem_cons_self).append (hp.append
                (List.singleton_sublist.mpr (List.mem_append.mpr (Or.inl List.mem_cons_self))))
            exact ha.not_abab hrot₁ u x₂ x₁ w₀ hs (Or.inl hu)
              (fun h => h.elim hx₂.1 fun h' => h'.2 hb₂) (Or.inr ⟨hx₁.2.1, hnb⟩) hwa

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece.exists_fourPiece

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPiece
