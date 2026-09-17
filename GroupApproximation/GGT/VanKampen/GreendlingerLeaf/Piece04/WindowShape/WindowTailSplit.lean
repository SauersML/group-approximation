import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplitCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the tail split of a run window

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-05`, endpoint module.

* `WindowTailSplit.split`: a nonempty run window `[x, y]` of class `i` whose end `y` is not strictly
  inside a gap ends with a dart `u`, and the class window is `rest ++ u :: γc`, where either
  `γc = []`, or `γc` is the whole (nonempty) gap after the side `s` of `u = side_s.last`, the next
  side `s'` of the class starts at `y` with `e = side_s'.head`, and `g = γc.last` is the class dart
  at `y - 1`.

This is steps 2 and 3 of the proof in `WindowShape.WindowTailSplitBlock`, from step 1
(`WindowTailSplitCore.tailSplitAt` at the sides of the class).  The target is proved in full; it
is the statement `WindowShape.TailShape.WindowTailSplitStatement` of lane gl-p04-07.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape

universe u w v

section TailSplit

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **Tail split of a run window** (lane gl-p04-05).  A nonempty run window ending off a gap ends
with `u`, and the class window is `rest ++ u :: γc` with `γc` empty or the whole gap after the side
of `u`. -/
theorem WindowTailSplit.split (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i x y : ℕ)
    (hi : i < Q.classCount k) (hxy : x ≤ y) (hy : y ≤ (Q.word k i).length)
    (hng : ¬ Q.InGap k i y) (hne : Q.runWindow k i x y ≠ []) :
    ∃ (u : S.diagram.toCombMap.Dart) (U' γc rest : List S.diagram.toCombMap.Dart),
      Q.runWindow k i x y = U' ++ [u] ∧ Q.classWindow k i x y = rest ++ u :: γc ∧
      (γc = [] ∨ ∃ (n s s' : ℕ) (e g : S.diagram.toCombMap.Dart),
        (Q.classDarts k i)[y]? = some e ∧ (Q.classDarts k i)[y - 1]? = some g ∧
        γc.getLast? = some g ∧ γc = Q.gap k s ∧ (Q.classSides k i)[n]? = some s ∧
        (Q.classSides k i)[n + 1]? = some s' ∧ (P.sideDarts k s).getLast? = some u ∧
        (P.sideDarts k s').head? = some e) := by
  have hngRec : ¬ Q.InGapRec k (Q.classSides k i) y := by
    intro h
    have h' := OsinLemma94ClassPolygons.inGap_of_inGapRec Q k (Q.classSides k i) [] y
      (List.nil_append _).symm h
    simp only [List.flatMap_nil, List.length_nil, Nat.zero_add] at h'
    exact hng h'
  have hlen : (Q.word k i).length = (Q.classDarts k i).length := by
    simp only [OsinLemma94ClassPolygons.word, Embedded.dartWord, List.length_map]
  have hsides : ∀ t ∈ Q.classSides k i, P.sideDarts k t ≠ [] :=
    fun t ht => P.side_ne_nil k t (Q.lt_sideCount_of_mem k i hi t ht)
  have hlt : Q.runPos k (Q.classSides k i) x < Q.runPos k (Q.classSides k i) y := by
    by_contra hge
    have heq : Q.runPos k (Q.classSides k i) x = Q.runPos k (Q.classSides k i) y :=
      Nat.le_antisymm (Q.runPos_mono k (Q.classSides k i) hxy) (Nat.le_of_not_lt hge)
    apply hne
    show ((Q.sideRun k i).drop (Q.runPos k (Q.classSides k i) x)).take
      (Q.runPos k (Q.classSides k i) y - Q.runPos k (Q.classSides k i) x) = []
    rw [heq, Nat.sub_self, List.take_zero]
  have hy' : y ≤ ((Q.classSides k i).flatMap fun t => P.sideDarts k t ++ Q.gap k t).length := by
    have hcd : Q.classDarts k i =
        (Q.classSides k i).flatMap fun t => P.sideDarts k t ++ Q.gap k t := rfl
    rw [← hcd]
    omega
  have hpos : 0 < Q.runPos k (Q.classSides k i) y := by omega
  obtain ⟨u, pre, γc, hT, hu, hpre, hdisj⟩ :=
    WindowTailSplit.tailSplitAt Q k (Q.classSides k i) y hsides (Q.gap_last k i hi) hy' hngRec
      hpos
  have hxpre : x ≤ pre.length := by
    by_contra hx
    have hm := Q.runPos_mono k (Q.classSides k i) (show pre.length + 1 ≤ x by omega)
    omega
  obtain ⟨U', hU'⟩ := WindowTailSplit.take_drop_eq_append_last hlt hu
  refine ⟨u, U', γc, pre.drop x, hU', ?_, ?_⟩
  · show (((Q.classSides k i).flatMap fun t => P.sideDarts k t ++ Q.gap k t).drop x).take
      (y - x) = pre.drop x ++ u :: γc
    rw [← List.drop_take, hT, List.drop_append_of_le_length hxpre]
  · rcases hdisj with h0 | ⟨n, s, s', e, hBy, hγ, hn, hn1, hul, he⟩
    · exact Or.inl h0
    · by_cases hγ0 : γc = []
      · exact Or.inl hγ0
      · have hlenT : (((Q.classSides k i).flatMap fun t => P.sideDarts k t ++ Q.gap k t).take
            y).length = y := List.length_take_of_le hy'
        have hTlen := congrArg List.length hT
        rw [hlenT, List.length_append, List.length_cons] at hTlen
        have hy1 : y - 1 < y := by omega
        obtain ⟨g, hg⟩ : ∃ g, γc.getLast? = some g := ⟨_, List.getLast?_eq_some_getLast hγ0⟩
        have happ : pre ++ u :: γc = (pre ++ [u]) ++ γc := by
          rw [List.append_assoc, List.singleton_append]
        have hTl : (((Q.classSides k i).flatMap fun t => P.sideDarts k t ++ Q.gap k t).take
            y).getLast? = some g := by
          rw [hT, happ, List.getLast?_append, hg, Option.some_or]
        rw [List.getLast?_eq_getElem?, hlenT, List.getElem?_take_of_lt hy1] at hTl
        exact Or.inr ⟨n, s, s', e, g, hBy, hTl, hg, hγ, hn, hn1, hul, he⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit.split

end TailSplit

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape
