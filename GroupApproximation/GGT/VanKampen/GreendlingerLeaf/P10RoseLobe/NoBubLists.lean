import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.PlaceLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Placement of a non-bubble block: list lemmas

Lane gl-p10-58.  Pure list facts behind `NoBubStatement`.  The cycle is `A ++ B ++ C` with a
contiguous block `B`, and a Boolean predicate `P` either removes `B` and keeps `A ++ C` (rm form)
or keeps `B` and removes `A ++ C` (kp form).

* Source side (`roseLobeNoBub_src`): for an infix `I` of the nodup cycle, `I.filter P` is an
  infix of `I` if `P` removes `A ++ C`, or some dart of `B` is off `I`, or `B` is a prefix or a
  suffix of `I`.  Only the rm-form bubble strictly inside `I` is excluded.
* Target side (`roseLobeNoBub_tgt`): for a suffix `T` of the cycle, `T.filter P` is a *prefix* of
  `T` if `B` avoids `T`, or `C = []` and `P` removes `B`, or `P` removes `A ++ C` and `A` avoids
  `T`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section Lists

variable {α : Type*}

/-- A member of `A ++ B ++ C` outside `B` lies in `A ++ C`. -/
theorem roseLobeNoBub_mem_split {a : α} {A B C : List α} (hm : a ∈ A ++ B ++ C) (hB : a ∉ B) :
    a ∈ A ++ C := by
  rcases List.mem_append.mp hm with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left C h
    · exact absurd h hB
  · exact List.mem_append_right A h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_mem_split

/-- **Source side, kp form**: `P` keeps `B` and removes `A ++ C`, so the filter of any infix is an
infix. -/
theorem roseLobeNoBub_src_kp {P : α → Bool} {S I T A B C : List α}
    (h : S ++ I ++ T = A ++ B ++ C) (hB : B.filter P = B) (hAC : (A ++ C).filter P = []) :
    I.filter P <:+: I :=
  roseLobePlace_filter_infix h (v := false) (w := true)
    (fun a ha => Bool.eq_false_iff.mpr
      (List.filter_eq_nil_iff.mp hAC a (List.mem_append_left C ha)))
    (fun a ha => List.filter_eq_self.mp hB a ha)
    (fun a ha => Bool.eq_false_iff.mpr
      (List.filter_eq_nil_iff.mp hAC a (List.mem_append_right A ha)))
    (fun hv _ => absurd hv (by decide))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_src_kp

/-- **Source side, rm form, block at an end**: `P` removes `B` and keeps `A ++ C`, and `B` is a
prefix or a suffix of the nodup infix `I`; then the filter is the rest of `I`. -/
theorem roseLobeNoBub_src_end {P : α → Bool} {S I T A B C : List α}
    (h : S ++ I ++ T = A ++ B ++ C) (hnd : I.Nodup) (hB : B.filter P = [])
    (hAC : (A ++ C).filter P = A ++ C) (hBI : B <+: I ∨ B <:+ I) : I.filter P <:+: I := by
  have hkeep : ∀ q ∈ I, q ∉ B → P q = true := fun q hq hqB =>
    List.filter_eq_self.mp hAC q (roseLobeNoBub_mem_split
      (by rw [← h]; exact List.mem_append_left T (List.mem_append_right S hq)) hqB)
  rcases hBI with ⟨Q, rfl⟩ | ⟨Q, rfl⟩
  · have hd := List.nodup_append.mp hnd
    have hQ : Q.filter P = Q := List.filter_eq_self.mpr fun q hq =>
      hkeep q (List.mem_append_right B hq) fun hqB => hd.2.2 q hqB q hq rfl
    rw [List.filter_append, hB, hQ, List.nil_append]
    exact (List.suffix_append B Q).isInfix
  · have hd := List.nodup_append.mp hnd
    have hQ : Q.filter P = Q := List.filter_eq_self.mpr fun q hq =>
      hkeep q (List.mem_append_left B hq) fun hqB => hd.2.2 q hq q hqB rfl
    rw [List.filter_append, hQ, hB, List.append_nil]
    exact (List.prefix_append Q B).isInfix

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_src_end

/-- **Source side of a non-bubble block.**  For an infix `I` of the nodup cycle
`S ++ I ++ T = A ++ B ++ C` with a contiguous block `B`, the filter `I.filter P` is an infix of
`I` if `P` removes `A ++ C`, or a dart of `B` is off `I`, or `B` is a prefix or suffix of `I`. -/
theorem roseLobeNoBub_src {P : α → Bool} {S I T A B C : List α}
    (h : S ++ I ++ T = A ++ B ++ C) (hnd : (A ++ B ++ C).Nodup)
    (hblk : (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ []))
    (hpos : (A ++ C).filter P = [] ∨ (∃ d ∈ B, d ∉ I) ∨ B <+: I ∨ B <:+ I) :
    I.filter P <:+: I := by
  have hI : I.Nodup := (List.infix_append S I T).sublist.nodup (by rw [h]; exact hnd)
  rcases hpos with hnil | hesc | hBI
  · rcases hblk with ⟨-, hAC, hne⟩ | ⟨hB, -, -⟩
    · exact absurd (hAC.symm.trans hnil) hne
    · exact roseLobeNoBub_src_kp h hB hnil
  · exact roseLobePlace_filter_block h hblk hesc
  · rcases hblk with ⟨hB, hAC, -⟩ | ⟨hB, hAC, -⟩
    · exact roseLobeNoBub_src_end h hI hB hAC hBI
    · exact roseLobeNoBub_src_kp h hB hAC

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_src

/-- **Target side, `B` avoids `T`**: then `T` lies in `A ++ C`, on which `P` is constant, so the
filter is `T` or `[]`. -/
theorem roseLobeNoBub_tgt_avoid {P : α → Bool} {S T A B C : List α}
    (h : S ++ T = A ++ B ++ C)
    (hblk : (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ []))
    (hBT : ∀ d ∈ B, d ∉ T) : T.filter P <+: T := by
  have hm : ∀ q ∈ T, q ∈ A ++ C := fun q hq => roseLobeNoBub_mem_split
    (by rw [← h]; exact List.mem_append_right S hq) (fun hqB => hBT q hqB hq)
  rcases hblk with ⟨-, hAC, -⟩ | ⟨-, hAC, -⟩
  · have hf : T.filter P = T := List.filter_eq_self.mpr fun q hq =>
      List.filter_eq_self.mp hAC q (hm q hq)
    rw [hf]
    exact List.prefix_refl T
  · have hf : T.filter P = [] := List.filter_eq_nil_iff.mpr fun q hq =>
      List.filter_eq_nil_iff.mp hAC q (hm q hq)
    rw [hf]
    exact List.nil_prefix

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_tgt_avoid

/-- **Target side, removed block at the end of the cycle**: `C = []` and `P` removes `B`.  Then
`T` is a kept piece of `A` followed by `B`, or `T` lies inside `B`. -/
theorem roseLobeNoBub_tgt_end {P : α → Bool} {S T A B C : List α}
    (h : S ++ T = A ++ B ++ C) (hC : C = [])
    (hblk : (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ []))
    (hBf : B.filter P = []) : T.filter P <+: T := by
  subst hC
  rcases hblk with ⟨-, hAC, -⟩ | ⟨hB, -, hne⟩
  · rw [List.append_nil] at h hAC
    rcases List.append_eq_append_iff.mp h with ⟨as, hA, hT⟩ | ⟨bs, -, hB'⟩
    · have has : as.filter P = as := List.filter_eq_self.mpr fun q hq =>
        List.filter_eq_self.mp hAC q (by rw [hA]; exact List.mem_append_right S hq)
      rw [hT, List.filter_append, has, hBf, List.append_nil]
      exact List.prefix_append as B
    · have hf : T.filter P = [] := List.filter_eq_nil_iff.mpr fun q hq =>
        List.filter_eq_nil_iff.mp hBf q (by rw [hB']; exact List.mem_append_right bs hq)
      rw [hf]
      exact List.nil_prefix
  · exact absurd (hB.symm.trans hBf) hne

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_tgt_end

/-- **Target side, kp form with `A` off `T`**: `P` keeps `B` and removes `A ++ C`, and no dart of
`A` is on `T`.  Then `T` is `B ++ C`, or lies inside `C`, or is a tail of `B` followed by `C`. -/
theorem roseLobeNoBub_tgt_kp {P : α → Bool} {S T A B C : List α}
    (h : S ++ T = A ++ B ++ C) (hB : B.filter P = B) (hAC : (A ++ C).filter P = [])
    (hAT : ∀ d ∈ A, d ∉ T) : T.filter P <+: T := by
  have hC : ∀ q ∈ C, ¬P q = true := fun q hq =>
    List.filter_eq_nil_iff.mp hAC q (List.mem_append_right A hq)
  have hCf : C.filter P = [] := List.filter_eq_nil_iff.mpr hC
  rw [List.append_assoc] at h
  rcases List.append_eq_append_iff.mp h with ⟨as, hA', hT⟩ | ⟨bs, -, h2⟩
  · have has : as = [] := List.eq_nil_iff_forall_not_mem.mpr fun q hq =>
      hAT q (by rw [hA']; exact List.mem_append_right S hq)
        (by rw [hT]; exact List.mem_append_left (B ++ C) hq)
    rw [hT, has, List.nil_append, List.filter_append, hB, hCf, List.append_nil]
    exact List.prefix_append B C
  · rcases List.append_eq_append_iff.mp h2 with ⟨cs, -, hC'⟩ | ⟨ds, hB', hT⟩
    · have hf : T.filter P = [] := List.filter_eq_nil_iff.mpr fun q hq =>
        hC q (by rw [hC']; exact List.mem_append_right cs hq)
      rw [hf]
      exact List.nil_prefix
    · have hds : ds.filter P = ds := List.filter_eq_self.mpr fun q hq =>
        List.filter_eq_self.mp hB q (by rw [hB']; exact List.mem_append_right bs hq)
      rw [hT, List.filter_append, hds, hCf, List.append_nil]
      exact List.prefix_append ds C

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_tgt_kp

/-- **Target side of a non-bubble block.**  For a suffix `T` of the cycle
`S ++ T = A ++ B ++ C` with a contiguous block `B`, the filter `T.filter P` is a prefix of `T` if
`B` avoids `T`, or `C = []` and `P` removes `B`, or `P` removes `A ++ C` and `A` avoids `T`. -/
theorem roseLobeNoBub_tgt {P : α → Bool} {S T A B C : List α}
    (h : S ++ T = A ++ B ++ C)
    (hblk : (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ []))
    (hpos : (∀ d ∈ B, d ∉ T) ∨ (C = [] ∧ B.filter P = []) ∨
      ((A ++ C).filter P = [] ∧ ∀ d ∈ A, d ∉ T)) :
    T.filter P <+: T := by
  rcases hpos with hBT | ⟨hC, hBf⟩ | ⟨hAC, hAT⟩
  · exact roseLobeNoBub_tgt_avoid h hblk hBT
  · exact roseLobeNoBub_tgt_end h hC hblk hBf
  · rcases hblk with ⟨-, hAC', hne⟩ | ⟨hB, -, -⟩
    · exact absurd (hAC'.symm.trans hAC) hne
    · exact roseLobeNoBub_tgt_kp h hB hAC hAT

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_tgt

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
