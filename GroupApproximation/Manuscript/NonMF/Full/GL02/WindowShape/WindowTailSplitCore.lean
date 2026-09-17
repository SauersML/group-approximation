import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.WindowTailSplitBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the tail split over the sides of a class

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.WindowTailSplitCore`
(origin/main blob `bbebeff7d`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-05`, second module.
This is step 1 of the proof in `WindowShape.WindowTailSplitBlock`, by recursion over the sides
`L`.

* `tailSplitAt`: over nonempty sides whose last gap is empty, a position `y ≤ |B|` that is not
  strictly inside a gap and has a positive side-run position satisfies `TailSplitAt`.  At the first
  block `side_s ++ gap_s`: `y ≤ |side_s|` is case (a) (`tailSplitAt_first`); `|side_s| < y ≤
  |side_s| + |gap_s|` forces `y = |side_s| + |gap_s|`, case (b) (`tailSplitAt_end`); otherwise
  recurse at `y - |side_s| - |gap_s|` over `L` and shift the prefix by the first block and the side
  index by one.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.WindowTailSplit

universe u w v

section Core

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **The tail split over the sides `L`** (step 1 of the proof in `WindowTailSplitBlock`). -/
theorem tailSplitAt (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    ∀ (L : List ℕ) (y : ℕ), (∀ t ∈ L, P.sideDarts k t ≠ []) →
      (∀ t ∈ L.getLast?, Q.gap k t = []) →
      y ≤ (L.flatMap fun t => P.sideDarts k t ++ Q.gap k t).length → ¬ Q.InGapRec k L y →
      0 < Q.runPos k L y → TailSplitAt Q k L y
  | [], _, _, _, _, _, hpos => by simp [OsinLemma94ClassPolygons.runPos] at hpos
  | s :: L, y, hne, hlast, hy, hng, hpos => by
    have e1 : (P.word k s).length = (P.sideDarts k s).length := by
      simp only [OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.length_map]
    have e2 : (Embedded.dartWord S.diagram (Q.gap k s)).length = (Q.gap k s).length := by
      simp only [Embedded.dartWord, List.length_map]
    have hB : ((s :: L).flatMap fun t => P.sideDarts k t ++ Q.gap k t) =
        (P.sideDarts k s ++ Q.gap k s) ++ L.flatMap fun t => P.sideDarts k t ++ Q.gap k t :=
      List.flatMap_cons
    rw [hB] at hy
    simp only [List.length_append] at hy
    by_cases h1 : y ≤ (P.sideDarts k s).length
    · exact tailSplitAt_first Q k s L y h1 hpos
    by_cases h2 : y ≤ (P.sideDarts k s).length + (Q.gap k s).length
    · have hy2 : y = (P.sideDarts k s).length + (Q.gap k s).length := by
        by_contra hne2
        apply hng
        rw [OsinLemma94ClassPolygons.InGapRec]
        exact Or.inl ⟨by omega, by omega⟩
      exact tailSplitAt_end Q k s L y hne hlast hy2
    have hy3 : (P.sideDarts k s).length + (Q.gap k s).length < y := by omega
    have hc1 : ¬ y ≤ (P.word k s).length := by omega
    have hc2 : ¬ y ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
      omega
    have hrp : Q.runPos k (s :: L) y = (P.sideDarts k s).length +
        Q.runPos k L (y - (P.sideDarts k s).length - (Q.gap k s).length) := by
      rw [OsinLemma94ClassPolygons.runPos, if_neg hc1, if_neg hc2, e1, e2]
    have hng' : ¬ Q.InGapRec k L (y - (P.sideDarts k s).length - (Q.gap k s).length) := by
      intro h
      apply hng
      rw [OsinLemma94ClassPolygons.InGapRec, e1, e2]
      exact Or.inr ⟨by omega, h⟩
    have hneL : ∀ t ∈ L, P.sideDarts k t ≠ [] := fun t ht => hne t (List.mem_cons_of_mem s ht)
    have hyL : y - (P.sideDarts k s).length - (Q.gap k s).length ≤
        (L.flatMap fun t => P.sideDarts k t ++ Q.gap k t).length := by
      omega
    have hlastL : ∀ t ∈ L.getLast?, Q.gap k t = [] := by
      intro t ht
      apply hlast
      cases L with
      | nil => simp at ht
      | cons s' L' =>
        rw [List.getLast?_cons_cons]
        exact ht
    have hposL : 0 < Q.runPos k L (y - (P.sideDarts k s).length - (Q.gap k s).length) := by
      cases L with
      | nil =>
        simp only [List.flatMap_nil, List.length_nil] at hyL
        omega
      | cons s' L' =>
        have hs' : 0 < (P.sideDarts k s').length :=
          List.length_pos_iff.mpr (hneL s' List.mem_cons_self)
        have e1' : (P.word k s').length = (P.sideDarts k s').length := by
          simp only [OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.length_map]
        rw [OsinLemma94ClassPolygons.runPos]
        split_ifs <;> omega
    obtain ⟨u, pre, γc, hT, hu, hpre, hdisj⟩ :=
      tailSplitAt Q k L (y - (P.sideDarts k s).length - (Q.gap k s).length) hneL hlastL hyL hng'
        hposL
    have hlenle : (P.sideDarts k s ++ Q.gap k s).length ≤ y := by
      rw [List.length_append]
      omega
    unfold TailSplitAt
    rw [hB, List.flatMap_cons, hrp]
    refine ⟨u, (P.sideDarts k s ++ Q.gap k s) ++ pre, γc, ?_, ?_, ?_, ?_⟩
    · rw [List.take_append, List.take_of_length_le hlenle, List.length_append, ← Nat.sub_sub, hT]
      simp only [List.append_assoc]
    · have hidx : (P.sideDarts k s).length ≤ (P.sideDarts k s).length +
          Q.runPos k L (y - (P.sideDarts k s).length - (Q.gap k s).length) - 1 := by
        omega
      have hsub : (P.sideDarts k s).length +
          Q.runPos k L (y - (P.sideDarts k s).length - (Q.gap k s).length) - 1 -
            (P.sideDarts k s).length =
          Q.runPos k L (y - (P.sideDarts k s).length - (Q.gap k s).length) - 1 := by
        omega
      rw [List.getElem?_append_right hidx, hsub]
      exact hu
    · have hlp : ((P.sideDarts k s ++ Q.gap k s) ++ pre).length =
          (P.sideDarts k s).length + (Q.gap k s).length + pre.length := by
        simp only [List.length_append]
      have hc1' : ¬ ((P.sideDarts k s ++ Q.gap k s) ++ pre).length + 1 ≤ (P.word k s).length := by
        omega
      have hc2' : ¬ ((P.sideDarts k s ++ Q.gap k s) ++ pre).length + 1 ≤
          (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
        omega
      have hc3 : ((P.sideDarts k s ++ Q.gap k s) ++ pre).length + 1 - (P.word k s).length -
          (Embedded.dartWord S.diagram (Q.gap k s)).length = pre.length + 1 := by
        omega
      rw [OsinLemma94ClassPolygons.runPos, if_neg hc1', if_neg hc2', hc3, hpre, e1]
    · rcases hdisj with h0 | ⟨n, s₀, s₀', e, hBy, hγ, hn, hn1, hul, he⟩
      · exact Or.inl h0
      · refine Or.inr ⟨n + 1, s₀, s₀', e, ?_, hγ, ?_, ?_, hul, he⟩
        · rw [List.getElem?_append_right hlenle, List.length_append, ← Nat.sub_sub]
          exact hBy
        · rw [List.getElem?_cons_succ]
          exact hn
        · rw [List.getElem?_cons_succ]
          exact hn1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.WindowTailSplit.tailSplitAt

end Core

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.WindowTailSplit
