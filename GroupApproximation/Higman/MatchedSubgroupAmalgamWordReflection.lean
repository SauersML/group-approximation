import GroupApproximation.Higman.MatchedSubgroupAmalgam

/-!
# Letter reflection for matched sub-amalgams

Normalizing a reduced amalgam word only transfers edge elements between
adjacent letters.  Consequently membership of every letter in prescribed
factor subgroups containing the edge is invariant under normalization.  This
is the local normal-form input for reflecting membership in a matched
sub-amalgam.
-/

namespace GroupApproximation

open Monoid

namespace MatchedSubgroupAmalgamWordReflection

universe uι uH uG

variable {ι : Type uι} {H : Type uH} {G : ι → Type uG}
  [Group H] [∀ i, Group (G i)]

/-- Every reduced word admits a normal representative, and normalization
preserves the property that all letters belong to factor subgroups containing
the edge images. -/
theorem Reduced.exists_normalWord_prod_eq_mem_iff
    (φ : ∀ i, H →* G i)
    (d : PushoutI.NormalWord.Transversal φ)
    (S : ∀ i, Subgroup (G i))
    (hbase : ∀ i, (φ i).range ≤ S i) :
    ∀ {w : CoprodI.Word G}, PushoutI.Reduced φ w →
      ∃ w' : PushoutI.NormalWord d,
        w'.prod = PushoutI.ofCoprodI w.prod ∧
        w'.toList.map Sigma.fst = w.toList.map Sigma.fst ∧
        ((∀ l ∈ w'.toList, l.2 ∈ S l.1) ↔
          ∀ l ∈ w.toList, l.2 ∈ S l.1) := by
  classical
  intro w hw
  induction w using CoprodI.Word.consRecOn with
  | empty =>
      refine ⟨PushoutI.NormalWord.empty, ?_, rfl, ?_⟩
      · simp [PushoutI.NormalWord.prod, CoprodI.Word.empty,
          CoprodI.Word.prod]
      simp [CoprodI.Word.empty]
  | @cons i g w hidx hg ih =>
      obtain ⟨w', hwprod, hwidx, hwmem⟩ :=
        ih (fun l hl ↦ hw l (List.mem_cons_of_mem _ hl))
      let n := (d.compl i).equiv (g * φ i w'.head)
      let nw := PushoutI.NormalWord.cons g w' (by
        rwa [CoprodI.Word.fstIdx, ← List.head?_map, hwidx,
          List.head?_map]) (hw ⟨i, g⟩ List.mem_cons_self)
      refine ⟨nw, ?_, ?_, ?_⟩
      · change (PushoutI.NormalWord.cons g w' _ _).prod = _
        rw [PushoutI.NormalWord.prod_cons, hwprod]
        simp [CoprodI.Word.prod]
      · simp [nw, hwidx]
      · have hnprod : (n.1 : G i) * (n.2 : G i) =
            g * φ i w'.head :=
          (d.compl i).equiv_fst_mul_equiv_snd _
        have hbaseLeft : (n.1 : G i) ∈ S i := hbase i n.1.property
        have hbaseRight : φ i w'.head ∈ S i :=
          hbase i ⟨w'.head, rfl⟩
        have hgn_iff : g ∈ S i ↔ (n.2 : G i) ∈ S i := by
          constructor
          · intro hgS
            rw [← mul_mem_cancel_left hbaseLeft,
              hnprod, mul_mem_cancel_right hbaseRight]
            exact hgS
          · intro hnS
            rw [← mul_mem_cancel_right hbaseRight,
              ← hnprod, mul_mem_cancel_left hbaseLeft]
            exact hnS
        constructor
        · intro hnwall l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · apply hgn_iff.mpr
            exact hnwall ⟨i, (n.2 : G i)⟩ (by
              simp [nw, PushoutI.NormalWord.cons, n])
          · apply hwmem.mp
              (fun l hl ↦ hnwall l (by
                simp [nw, PushoutI.NormalWord.cons, hl])) l hl
        · intro hwall l hl
          have hgS : g ∈ S i := hwall ⟨i, g⟩ List.mem_cons_self
          have htail : ∀ l ∈ w'.toList, l.2 ∈ S l.1 :=
            hwmem.mpr (fun l hl ↦
              hwall l (List.mem_cons_of_mem _ hl))
          rw [show nw.toList = ⟨i, (n.2 : G i)⟩ :: w'.toList by
            rfl] at hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact hgn_iff.mp hgS
          · exact htail l hl

end MatchedSubgroupAmalgamWordReflection
end GroupApproximation
