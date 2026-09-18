import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplitAux
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the head split of a run window

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-04`, endpoint.

`WindowHeadSplit.split`: let `x ≤ y ≤ |word k i|`, where `x` is not strictly inside a gap and the
run window `runWindow k i x y` is nonempty.  Then the run window starts with a dart `t`, and the
class window is `γc ++ t :: rest`.  Either `γc = []`, or `γc` is the whole gap after a side `s` of
the class: the dart at `x - 1` is the last dart of `s`, the dart at `x` is the first dart of the
gap, and `t` is the first dart of the next side `s'` of the class.

The proof applies `split_aux` to the sides of the class.  Every side has a nonempty dart list
(`side_ne_nil`), `x` is outside `InGapRec` by `inGap_of_inGapRec`, and a nonempty run window
means the side-run position strictly increases from `x` to `y`.  Both windows are then cut at
their lengths.

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

/-- **Head split of a run window at a non-gap start** (lane gl-p04-04). -/
theorem split (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i x y : ℕ)
    (hi : i < Q.classCount k) (_hxy : x ≤ y) (_hy : y ≤ (Q.word k i).length)
    (hng : ¬ Q.InGap k i x) (hne : Q.runWindow k i x y ≠ []) :
    ∃ (t : S.diagram.toCombMap.Dart) (T' γc rest : List S.diagram.toCombMap.Dart),
      Q.runWindow k i x y = t :: T' ∧ Q.classWindow k i x y = γc ++ t :: rest ∧
      (γc = [] ∨ ∃ (n s s' : ℕ) (d w : S.diagram.toCombMap.Dart), 0 < x ∧
        (Q.classDarts k i)[x - 1]? = some d ∧ (Q.classDarts k i)[x]? = some w ∧
        γc.head? = some w ∧ γc = Q.gap k s ∧ (Q.classSides k i)[n]? = some s ∧
        (Q.classSides k i)[n + 1]? = some s' ∧ (P.sideDarts k s).getLast? = some d ∧
        (P.sideDarts k s').head? = some t) := by
  have hne' : ∀ s ∈ Q.classSides k i, P.sideDarts k s ≠ [] :=
    fun s hs => P.side_ne_nil k s (Q.lt_sideCount_of_mem k i hi s hs)
  have hngRec : ¬ Q.InGapRec k (Q.classSides k i) x := by
    intro h
    have h' := Q.inGap_of_inGapRec k (Q.classSides k i) [] x (List.nil_append _).symm h
    simp only [List.flatMap_nil, List.length_nil, Nat.zero_add] at h'
    exact hng h'
  have hlt : Q.runPos k (Q.classSides k i) x < Q.runPos k (Q.classSides k i) y := by
    by_contra hge
    apply hne
    rw [OsinLemma94ClassPolygons.runWindow, Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hge),
      List.take_zero]
  obtain ⟨t, R, γc, rest, hR, hrest, hlen, hcase⟩ :=
    split_aux Q k (Q.classSides k i) x y hne' hngRec hlt
  obtain ⟨m, hm⟩ : ∃ m : ℕ,
      Q.runPos k (Q.classSides k i) y - Q.runPos k (Q.classSides k i) x = m + 1 :=
    ⟨Q.runPos k (Q.classSides k i) y - Q.runPos k (Q.classSides k i) x - 1, by omega⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, y - x = γc.length + (m' + 1) :=
    ⟨y - x - γc.length - 1, by omega⟩
  refine ⟨t, R.take m, γc, rest.take m', ?_, ?_, hcase⟩
  · rw [OsinLemma94ClassPolygons.runWindow, OsinLemma94ClassPolygons.sideRun, hR, hm,
      List.take_succ_cons]
  · rw [OsinLemma94ClassPolygons.classWindow, OsinLemma94ClassPolygons.classDarts, hrest, hm',
      List.take_length_add_append, List.take_succ_cons]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.split

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit
