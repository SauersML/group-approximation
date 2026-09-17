import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplitBasic
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the head split on a list of sides

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-04`, second module.

`split_aux` walks a list `L` of sides with nonempty dart lists.  Suppose `x` is not strictly
inside a gap and the side-run position strictly increases from `x` to `y`.  Then the side run
from the side-run position of `x` starts with a dart `t`.  The class darts from `x` are a
(possibly empty) block `γc` followed by `t`, and `x + |γc| < y`.  When `γc` is nonempty, it is the
whole gap after a side `L[n]`: the dart before `x` is the last dart of that side, the dart at `x`
is the first dart of the gap, and `t` is the first dart of the next side `L[n+1]`.

The proof follows the `runPos` recursion:

* `x` inside the first side: `γc = []`;
* `x` at the end of the first side: `γc` is the first gap;
* `x` strictly inside the first gap is excluded;
* `x` at the end of the first gap: `γc = []`;
* past the first gap: recurse.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **The head split on a list of sides.**  The side run from `runPos L x` starts with `t`.  The
class darts from `x` are a block `γc` and then `t`, with `x + |γc| < y`.  Either `γc = []`, or
`γc` is the gap after `L[n]`, sitting between the last dart of `L[n]` and the first dart `t` of
`L[n+1]`. -/
theorem split_aux (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    ∀ (L : List ℕ) (x y : ℕ), (∀ s ∈ L, P.sideDarts k s ≠ []) → ¬ Q.InGapRec k L x →
      Q.runPos k L x < Q.runPos k L y →
      ∃ (t : S.diagram.toCombMap.Dart) (R γc rest : List S.diagram.toCombMap.Dart),
        (L.flatMap (P.sideDarts k)).drop (Q.runPos k L x) = t :: R ∧
        (L.flatMap fun r => P.sideDarts k r ++ Q.gap k r).drop x = γc ++ t :: rest ∧
        x + γc.length < y ∧
        (γc = [] ∨ ∃ (n s s' : ℕ) (d w : S.diagram.toCombMap.Dart), 0 < x ∧
          (L.flatMap fun r => P.sideDarts k r ++ Q.gap k r)[x - 1]? = some d ∧
          (L.flatMap fun r => P.sideDarts k r ++ Q.gap k r)[x]? = some w ∧
          γc.head? = some w ∧ γc = Q.gap k s ∧ L[n]? = some s ∧ L[n + 1]? = some s' ∧
          (P.sideDarts k s).getLast? = some d ∧ (P.sideDarts k s').head? = some t)
  | [], _, _, _, _, h => by simp [OsinLemma94ClassPolygons.runPos] at h
  | s :: L, x, y, hne, hng, hlt => by
    have e1 : (P.word k s).length = (P.sideDarts k s).length := by
      simp only [OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.length_map]
    have e2 : (Embedded.dartWord S.diagram (Q.gap k s)).length = (Q.gap k s).length := by
      simp only [Embedded.dartWord, List.length_map]
    have hside : P.sideDarts k s ≠ [] := hne s List.mem_cons_self
    have hpos : 0 < (P.sideDarts k s).length := List.length_pos_iff.mpr hside
    have hneL : ∀ r ∈ L, P.sideDarts k r ≠ [] := fun r hr => hne r (List.mem_cons_of_mem s hr)
    have hsr : (s :: L).flatMap (P.sideDarts k) =
        P.sideDarts k s ++ L.flatMap (P.sideDarts k) := List.flatMap_cons
    have hcd : ((s :: L).flatMap fun r => P.sideDarts k r ++ Q.gap k r) =
        P.sideDarts k s ++ (Q.gap k s ++ L.flatMap fun r => P.sideDarts k r ++ Q.gap k r) := by
      simp only [List.flatMap_cons, List.append_assoc]
    have hcd2 : ((s :: L).flatMap fun r => P.sideDarts k r ++ Q.gap k r) =
        (P.sideDarts k s ++ Q.gap k s) ++ L.flatMap fun r => P.sideDarts k r ++ Q.gap k r :=
      List.flatMap_cons
    have hB : (P.sideDarts k s ++ Q.gap k s).length =
        (P.sideDarts k s).length + (Q.gap k s).length := List.length_append
    by_cases h1 : x < (P.sideDarts k s).length
    · have hrx : Q.runPos k (s :: L) x = x := runPos_cons_of_le Q k s L x (by omega)
      refine ⟨(P.sideDarts k s)[x]'h1, (P.sideDarts k s).drop (x + 1) ++ L.flatMap (P.sideDarts k),
        [], (P.sideDarts k s).drop (x + 1) ++
          (Q.gap k s ++ L.flatMap fun r => P.sideDarts k r ++ Q.gap k r), ?_, ?_, ?_, Or.inl rfl⟩
      · rw [hrx, hsr, List.drop_append_of_le_length h1.le, List.drop_eq_getElem_cons h1,
          List.cons_append]
      · rw [hcd, List.drop_append_of_le_length h1.le, List.drop_eq_getElem_cons h1,
          List.cons_append, List.nil_append]
      · rw [List.length_nil, Nat.add_zero]
        exact lt_of_runPos_lt Q k (s :: L) x y hlt
    by_cases h2 : x = (P.sideDarts k s).length
    · have hrx : Q.runPos k (s :: L) x = (P.sideDarts k s).length :=
        (runPos_cons_of_le Q k s L x (by omega)).trans h2
      have hy : ¬ y ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
        intro hy
        have _hle := runPos_cons_le_of_le Q k s L y hy
        omega
      have hry := runPos_cons_of_gt Q k s L y hy
      obtain ⟨s', L'', t, R', rfl, hR'⟩ := exists_next_side Q k L
        (y - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length) hneL
        (by omega)
      refine ⟨t, R' ++ L''.flatMap (P.sideDarts k), Q.gap k s,
        (R' ++ Q.gap k s') ++ L''.flatMap fun r => P.sideDarts k r ++ Q.gap k r, ?_, ?_,
        by omega, ?_⟩
      · rw [hrx, hsr, List.drop_left]
        simp only [List.flatMap_cons, hR', List.cons_append]
      · rw [hcd, h2, List.drop_left]
        simp only [List.flatMap_cons, hR', List.cons_append, List.append_assoc]
      · by_cases hg : Q.gap k s = []
        · exact Or.inl hg
        · obtain ⟨w, G', hG'⟩ := List.exists_cons_of_ne_nil hg
          have hgpos : 0 < (Q.gap k s).length := List.length_pos_iff.mpr hg
          have hx1 : x - 1 < (P.sideDarts k s).length := by omega
          have hle0 : (P.sideDarts k s).length ≤ x := by omega
          have hlt0 : x - (P.sideDarts k s).length < (Q.gap k s).length := by omega
          refine Or.inr ⟨0, s, s', (P.sideDarts k s).getLast hside, w, by omega, ?_, ?_,
            by rw [hG', List.head?_cons], rfl, List.getElem?_cons_zero,
            by rw [List.getElem?_cons_succ, List.getElem?_cons_zero],
            List.getLast?_eq_getLast hside, by rw [hR', List.head?_cons]⟩
          · rw [hcd, List.getElem?_append_left hx1, h2]
            exact List.getLast?_eq_getElem?.symm.trans (List.getLast?_eq_getLast hside)
          · rw [hcd, List.getElem?_append_right hle0, List.getElem?_append_left hlt0, h2,
              Nat.sub_self, hG', List.getElem?_cons_zero]
    by_cases h3 : x < (P.sideDarts k s).length + (Q.gap k s).length
    · exact (hng (by
        rw [OsinLemma94ClassPolygons.InGapRec]
        exact Or.inl ⟨by omega, by omega⟩)).elim
    by_cases h4 : x = (P.sideDarts k s).length + (Q.gap k s).length
    · have hrx : Q.runPos k (s :: L) x = (P.sideDarts k s).length :=
        (runPos_cons_of_mid Q k s L x (by omega) (by omega)).trans e1
      have hy : ¬ y ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
        intro hy
        have _hle := runPos_cons_le_of_le Q k s L y hy
        omega
      have hry := runPos_cons_of_gt Q k s L y hy
      obtain ⟨s', L'', t, R', rfl, hR'⟩ := exists_next_side Q k L
        (y - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length) hneL
        (by omega)
      have hle2 : (P.sideDarts k s ++ Q.gap k s).length ≤ x := by omega
      refine ⟨t, R' ++ L''.flatMap (P.sideDarts k), [],
        (R' ++ Q.gap k s') ++ L''.flatMap fun r => P.sideDarts k r ++ Q.gap k r, ?_, ?_, ?_,
        Or.inl rfl⟩
      · rw [hrx, hsr, List.drop_left]
        simp only [List.flatMap_cons, hR', List.cons_append]
      · rw [hcd2, drop_append_of_length_le hle2,
          show x - (P.sideDarts k s ++ Q.gap k s).length = 0 by omega, List.drop_zero]
        simp only [List.flatMap_cons, hR', List.cons_append, List.nil_append, List.append_assoc]
      · rw [List.length_nil, Nat.add_zero]
        omega
    have hgt : ¬ x ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
      omega
    have hrx := runPos_cons_of_gt Q k s L x hgt
    have hy : ¬ y ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
      intro hy
      have _hle := runPos_cons_le_of_le Q k s L y hy
      omega
    have hry := runPos_cons_of_gt Q k s L y hy
    have hng' : ¬ Q.InGapRec k L
        (x - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length) :=
      fun h => hng (by
        rw [OsinLemma94ClassPolygons.InGapRec]
        exact Or.inr ⟨by omega, h⟩)
    obtain ⟨t, R, γc, rest, hR, hrest, hlen, hcase⟩ := split_aux Q k L
      (x - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length)
      (y - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length) hneL hng'
      (by omega)
    have hle2 : (P.sideDarts k s ++ Q.gap k s).length ≤ x := by omega
    refine ⟨t, R, γc, rest, ?_, ?_, by omega, ?_⟩
    · rw [hrx, hsr, drop_append_add_of_eq e1.symm]
      exact hR
    · rw [hcd2, drop_append_of_length_le hle2, show x - (P.sideDarts k s ++ Q.gap k s).length =
        x - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length by omega]
      exact hrest
    · rcases hcase with hnil | ⟨n, s₀, s₁, d, w, hx0, hd, hw, hhead, hgap, hs0, hs1, hlast, hfirst⟩
      · exact Or.inl hnil
      · have hle1 : (P.sideDarts k s ++ Q.gap k s).length ≤ x - 1 := by omega
        refine Or.inr ⟨n + 1, s₀, s₁, d, w, by omega, ?_, ?_, hhead, hgap, ?_, ?_, hlast, hfirst⟩
        · rw [hcd2, List.getElem?_append_right hle1, show x - 1 - (P.sideDarts k s ++
            Q.gap k s).length = x - (P.word k s).length -
              (Embedded.dartWord S.diagram (Q.gap k s)).length - 1 by omega]
          exact hd
        · rw [hcd2, List.getElem?_append_right hle2, show x - (P.sideDarts k s ++
            Q.gap k s).length = x - (P.word k s).length -
              (Embedded.dartWord S.diagram (Q.gap k s)).length by omega]
          exact hw
        · rw [List.getElem?_cons_succ]
          exact hs0
        · rw [List.getElem?_cons_succ]
          exact hs1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.split_aux

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit
