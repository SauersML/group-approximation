import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.Charging
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BoundaryJunctionBudget
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassJoinsBoundaryArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ShortSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: at most `n` boundary value failures

Target: `OsinLemma94BoundaryValueFailureCountInput`.  Summed over the relator polygons, the boundary
bad junctions whose gap reads a value other than `1` number at most `n`, the number of relator
cells.

Route.  A value failure junction `s` of a relator polygon `k` is a boundary side joining the next
side at kind level.  Both sides are windows of the outer darts (`sideDarts_window`); the last dart
`e` of side `s` is followed along the face of `k` by the first dart of the next side, so the gap of
the junction is `gap S.diagram e` and `e` is a value failure dart (`IsValueFailure`): the face of
`k` is not the outer face, and `k` has a cell side, so it is adjacent to a relator cell.  The last
dart determines the junction: its face recovers `k` (`face_injective`), and the sides of one polygon
are disjoint (`sideDarts_disjoint`).  So the junctions inject into a set of value failure darts,
which has at most `n` elements (`card_le_rCellCount`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The clauses of a value failure junction. -/
theorem valueFailure_spec (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s ∈ P.valueFailureJunctions k) :
    s < P.sideCount k ∧ P.KindJoins k s ∧ (∃ j, P.kind k s = .boundary j) ∧
      RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) ≠ 1 := by
  obtain ⟨hbb, hval⟩ := Finset.mem_filter.mp hs
  obtain ⟨hbad, hj⟩ := Finset.mem_filter.mp hbb
  obtain ⟨hr, hjoin, -⟩ := Finset.mem_filter.mp hbad
  exact ⟨Finset.mem_range.mp hr, hjoin, hj, hval⟩

/-- The darts of a boundary side are outer darts. -/
theorem mem_outerDarts_of_mem_boundarySide (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {s jc : ℕ} (hs : s < P.sideCount k) (hkind : P.kind k s = .boundary jc)
    {d : S.diagram.toCombMap.Dart} (hd : d ∈ P.sideDarts k s) : d ∈ outerDarts S.diagram := by
  obtain ⟨_, _, _, _, _, _, hwin⟩ := P.sideDarts_window hs hkind
  rw [hwin] at hd
  exact List.mem_of_mem_drop (List.mem_of_mem_take hd)

/-- The face of a relator polygon is adjacent to a relator cell. -/
theorem cell_clause (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    (hk : k ∈ P.relatorPolygons) {s : ℕ} (hs : s < P.sideCount k) {e : S.diagram.toCombMap.Dart}
    (he : e ∈ P.sideDarts k s) :
    ∃ x, S.diagram.toCombMap.faceOf x = S.diagram.toCombMap.faceOf e ∧
      ∃ C ∈ S.diagram.relatorCells,
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) = C.face := by
  obtain ⟨s₀, hs₀, j₀, hj₀⟩ := (Finset.mem_filter.mp hk).2
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (P.side_ne_nil k s₀ hs₀)
  refine ⟨d, (P.faceOf_of_mem_sideDarts hs₀ hd).trans (P.faceOf_of_mem_sideDarts hs he).symm,
    Embedded.cell S.diagram j₀, Embedded.cell_mem S.diagram j₀, ?_⟩
  exact ((S.diagram.faceBoundary (Embedded.cell S.diagram j₀).face).mem_iff _).mp
    (P.alpha_mem_cellDarts_of_mem_cellSideDarts hs₀ hj₀ hd)

/-- **The last dart of a value failure junction is a value failure dart.** -/
theorem exists_valueFailure (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    (hk : k ∈ P.relatorPolygons) {s : ℕ} (hs : s ∈ P.valueFailureJunctions k) :
    ∃ e, (P.sideDarts k s).getLast? = some e ∧ IsValueFailure S.diagram e := by
  obtain ⟨hlt, ⟨hkeq, -⟩, ⟨j, hj⟩, hval⟩ := valueFailure_spec P hs
  have hlt' : (s + 1) % P.sideCount k < P.sideCount k := Nat.mod_lt _ (by omega)
  obtain ⟨e, he⟩ : ∃ e, (P.sideDarts k s).getLast? = some e :=
    ⟨_, List.getLast?_eq_some_getLast (P.side_ne_nil k s hlt)⟩
  obtain ⟨e', he'⟩ : ∃ e', (P.sideDarts k ((s + 1) % P.sideCount k)).head? = some e' :=
    ⟨_, List.head?_eq_some_head (P.side_ne_nil k _ hlt')⟩
  have hj' : P.kind k ((s + 1) % P.sideCount k) = .boundary j := hkeq.symm.trans hj
  have hperm : S.diagram.toCombMap.facePerm e = e' :=
    P.facePerm_getLast_eq_head_mod hlt (Option.mem_def.mpr he) (Option.mem_def.mpr he')
  have heS := List.mem_of_getLast? he
  refine ⟨e, he, mem_outerDarts_of_mem_boundarySide P hlt hj heS, ?_, ?_, ?_,
    cell_clause P hk hlt heS⟩
  · rw [hperm]
    exact mem_outerDarts_of_mem_boundarySide P hlt' hj' (List.mem_of_head? he')
  · rw [P.faceOf_of_mem_sideDarts hlt heS]
    exact P.face_ne_outer k
  · unfold gap
    rw [hperm, ← P.junctionGap_boundary he he' hj]
    exact hval

/-- The last dart of a side, with a default. -/
noncomputable def lastDart (P : OsinLemma94RealizedPolygons S) (d0 : S.diagram.toCombMap.Dart)
    (J : Σ _ : Fin P.count, ℕ) : S.diagram.toCombMap.Dart :=
  ((P.sideDarts J.1 J.2).getLast?).getD d0

theorem image_isValueFailure (P : OsinLemma94RealizedPolygons S) (d0 : S.diagram.toCombMap.Dart)
    {T : Finset (Fin P.count)} (hT : T ⊆ P.relatorPolygons) :
    ∀ e ∈ (T.sigma fun k => P.valueFailureJunctions k).image (lastDart P d0),
      IsValueFailure S.diagram e := by
  intro e he
  obtain ⟨⟨k, s⟩, hJ, rfl⟩ := Finset.mem_image.mp he
  simp only [Finset.mem_sigma] at hJ
  obtain ⟨e₁, he₁, hG⟩ := exists_valueFailure P (hT hJ.1) hJ.2
  show IsValueFailure S.diagram (((P.sideDarts k s).getLast?).getD d0)
  rw [he₁, Option.getD_some]
  exact hG

/-- **The last dart determines the junction.** -/
theorem lastDart_injOn (P : OsinLemma94RealizedPolygons S) (d0 : S.diagram.toCombMap.Dart)
    {T : Finset (Fin P.count)} (hT : T ⊆ P.relatorPolygons) :
    Set.InjOn (lastDart P d0)
      (↑(T.sigma (fun k => P.valueFailureJunctions k)) : Set (Σ _ : Fin P.count, ℕ)) := by
  rintro ⟨k₁, s₁⟩ hJ₁ ⟨k₂, s₂⟩ hJ₂ hf
  simp only [Finset.mem_coe, Finset.mem_sigma] at hJ₁ hJ₂
  obtain ⟨e₁, he₁, -⟩ := exists_valueFailure P (hT hJ₁.1) hJ₁.2
  obtain ⟨e₂, he₂, -⟩ := exists_valueFailure P (hT hJ₂.1) hJ₂.2
  have hlt₁ := (valueFailure_spec P hJ₁.2).1
  have hlt₂ := (valueFailure_spec P hJ₂.2).1
  have hm₁ := List.mem_of_getLast? he₁
  have hm₂ := List.mem_of_getLast? he₂
  have hee : e₁ = e₂ := by
    have h₁ : lastDart P d0 ⟨k₁, s₁⟩ = e₁ := by
      show ((P.sideDarts k₁ s₁).getLast?).getD d0 = e₁
      rw [he₁, Option.getD_some]
    have h₂ : lastDart P d0 ⟨k₂, s₂⟩ = e₂ := by
      show ((P.sideDarts k₂ s₂).getLast?).getD d0 = e₂
      rw [he₂, Option.getD_some]
    exact h₁.symm.trans (hf.trans h₂)
  subst hee
  have hk : k₁ = k₂ := P.face_injective
    ((P.faceOf_of_mem_sideDarts hlt₁ hm₁).symm.trans (P.faceOf_of_mem_sideDarts hlt₂ hm₂))
  subst hk
  have hs : s₁ = s₂ := by
    by_contra hne
    exact P.sideDarts_disjoint _ hlt₁ hlt₂ hne hm₁ hm₂
  subst hs
  rfl

/-- **At most `n` value failures**, over any set of relator polygons. -/
theorem valueFailure_count (P : OsinLemma94RealizedPolygons S) {T : Finset (Fin P.count)}
    (hT : T ⊆ P.relatorPolygons) :
    ∑ k ∈ T, (P.valueFailureJunctions k).card ≤ Delta.rCellCount := by
  rw [← Finset.card_sigma T fun k => P.valueFailureJunctions k]
  refine le_trans ?_ (le_of_eq S.equiv.rCellCount_eq)
  rcases (T.sigma fun k => P.valueFailureJunctions k).eq_empty_or_nonempty with h0 | ⟨⟨k, s⟩, hJ⟩
  · rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  · simp only [Finset.mem_sigma] at hJ
    obtain ⟨d0, -, -⟩ := exists_valueFailure P (hT hJ.1) hJ.2
    exact (Finset.card_image_of_injOn (lastDart_injOn P d0 hT)).symm.le.trans
      (card_le_rCellCount S.diagram _ (image_isValueFailure P d0 hT))

/-- **Osin's Lemma 9.4, boundary value failures.** -/
theorem proof : OsinLemma94BoundaryValueFailureCountInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨0, fun _ _ => ⟨1, Nat.one_pos, fun _ _ _ _ _ _ _ _ _ _ _ _ P _ => ?_⟩⟩
  exact valueFailure_count P (Finset.filter_subset _ _)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.valueFailure_spec
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.mem_outerDarts_of_mem_boundarySide
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.cell_clause
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.exists_valueFailure
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.lastDart
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.image_isValueFailure
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.lastDart_injOn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.valueFailure_count
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.proof
