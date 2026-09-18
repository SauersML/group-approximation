import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDoublingTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through a transport of the family

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`HasCleanTwoGon` (`Estimating/OsinAppendixEulerTwoGonDoublingTransport`) asks for no loops, no
multiple edges, and a two-gon of `phiMapO` with no corner in its gap and no relator cell.  A
thickening step carries every region of the family to a region of the new family
(`RegionTransport`), with the same target profile, the same cells through a renumbering, and the
crossing darts through an embedding of darts.  This module collects what such a transport keeps: the
two combinatorial clauses, the components of shared ends, and the data of `Φ'_M`.

* `RegionTransport`, with `map_mem`, `exists_map_eq`, `sideCellO_map`, `noLoops`,
  `joinsCells_map`, `noMultipleEdges`, `sharesEndO_map`, `mem_linkedComponentO_map`.
* `extPhiData_of_leastArea`: the data of `Φ'_M` on any component, at least area.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

open Equiv Embedded Embedded.RegionCandidate

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A transport of a distinguished family**: every region goes to a region of the new family, with
the same target profile, cells renumbered, and crossing darts through an embedding of darts. -/
structure RegionTransport
    (S S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) where
  map : S.family ↪ RegionCandidate D eps S'.diagram
  family_eq : S'.family = S.family.attach.map map
  cellIndex : Fin S.diagram.rCellCount ≃ Fin S'.diagram.rCellCount
  source : ∀ a, (map a).2.source = cellIndex a.1.2.source
  target : ∀ a, (map a).2.target = a.1.2.target.map cellIndex
  profile : ∀ a, RegionCandidate.SameTargetProfile (map a) a.1
  darts : S.diagram.toCombMap.Dart ↪ S'.diagram.toCombMap.Dart
  cross : ∀ a s o, crossO (map a) s o = (crossO a.1 s o).map darts

namespace RegionTransport

variable {S S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  (T : RegionTransport S S')

theorem map_mem (a : S.family) : T.map a ∈ S'.family := by
  rw [T.family_eq]
  exact Finset.mem_map_of_mem _ (Finset.mem_attach _ _)

theorem exists_map_eq {b : RegionCandidate D eps S'.diagram} (hb : b ∈ S'.family) :
    ∃ a, T.map a = b := by
  rw [T.family_eq] at hb
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hb
  exact ⟨a, rfl⟩

theorem sideCellO_map (a : S.family) (s : Bool) :
    sideCellO (T.map a) s = (sideCellO a.1 s).map T.cellIndex := by
  cases s
  · exact T.target a
  · show some (T.map a).2.source = some (T.cellIndex a.1.2.source)
    rw [T.source]

include T in
theorem noLoops (h : S.NoLoops) : S'.NoLoops := by
  intro b hb
  obtain ⟨a, rfl⟩ := T.exists_map_eq hb
  rw [T.target, T.source]
  intro heq
  have heq' : Option.map T.cellIndex a.1.2.target =
      Option.map T.cellIndex (some a.1.2.source) := heq
  exact h a.1 a.2 (Option.map_injective T.cellIndex.injective heq')

theorem joinsCells_map (a : S.family) (i j : Fin S'.diagram.rCellCount) :
    (T.map a).JoinsCells i j ↔ a.1.JoinsCells (T.cellIndex.symm i) (T.cellIndex.symm j) := by
  have hs : ∀ k, (T.map a).2.source = k ↔ a.1.2.source = T.cellIndex.symm k := fun k => by
    rw [T.source, Equiv.apply_eq_iff_eq_symm_apply]
  have ht : ∀ k, (T.map a).2.target = some k ↔
      a.1.2.target = some (T.cellIndex.symm k) := fun k => by
    rw [T.target]
    constructor
    · intro h
      have h' : Option.map T.cellIndex a.1.2.target =
          Option.map T.cellIndex (some (T.cellIndex.symm k)) := by
        rw [h]
        simp
      exact Option.map_injective T.cellIndex.injective h'
    · intro h
      rw [h]
      simp
  simp only [RegionCandidate.JoinsCells, hs, ht]

include T in
theorem noMultipleEdges (h : S.NoMultipleEdges) : S'.NoMultipleEdges := by
  intro b hb b' hb' hne i j hi hj
  obtain ⟨a, rfl⟩ := T.exists_map_eq hb
  obtain ⟨a', rfl⟩ := T.exists_map_eq hb'
  exact h a.1 a.2 a'.1 a'.2 (fun heq => hne (by rw [show a = a' from Subtype.ext heq])) _ _
    ((T.joinsCells_map a i j).mp hi) ((T.joinsCells_map a' i j).mp hj)

theorem sharesEndO_map (a b : S.family) :
    SharesEndO S'.family (T.map a) (T.map b) ↔ SharesEndO S.family a.1 b.1 := by
  constructor
  · rintro ⟨-, -, s, t, hst⟩
    refine ⟨a.2, b.2, s, t, ?_⟩
    rw [T.sideCellO_map, T.sideCellO_map] at hst
    exact Option.map_injective T.cellIndex.injective hst
  · rintro ⟨-, -, s, t, hst⟩
    refine ⟨T.map_mem a, T.map_mem b, s, t, ?_⟩
    rw [T.sideCellO_map, T.sideCellO_map, hst]

theorem mem_linkedComponentO_map (a₀ : S.family) {b : RegionCandidate D eps S'.diagram} :
    b ∈ linkedComponentO S'.family (T.map a₀) ↔
      ∃ a : S.family, T.map a = b ∧ a.1 ∈ linkedComponentO S.family a₀.1 := by
  constructor
  · intro hb
    obtain ⟨-, hpath⟩ := mem_linkedComponentO.mp hb
    have key : ∀ b', Relation.ReflTransGen (SharesEndO S'.family) (T.map a₀) b' →
        ∃ a : S.family, T.map a = b' ∧ Relation.ReflTransGen (SharesEndO S.family) a₀.1 a.1 := by
      intro b' h
      induction h with
      | refl => exact ⟨a₀, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        obtain ⟨a, rfl, ha⟩ := ih
        obtain ⟨a', rfl⟩ := T.exists_map_eq hstep.2.1
        exact ⟨a', rfl, ha.tail ((T.sharesEndO_map a a').mp hstep)⟩
    obtain ⟨a, rfl, ha⟩ := key b hpath
    exact ⟨a, rfl, mem_linkedComponentO.mpr ⟨a.2, ha⟩⟩
  · rintro ⟨a, rfl, ha⟩
    obtain ⟨-, hpath⟩ := mem_linkedComponentO.mp ha
    have key : ∀ x, Relation.ReflTransGen (SharesEndO S.family) a₀.1 x → ∀ hx : x ∈ S.family,
        Relation.ReflTransGen (SharesEndO S'.family) (T.map a₀) (T.map ⟨x, hx⟩) := by
      intro x h
      induction h with
      | refl => exact fun _ => Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        exact fun hx => (ih hstep.1).tail ((T.sharesEndO_map ⟨_, hstep.1⟩ ⟨_, hx⟩).mpr hstep)
    exact mem_linkedComponentO.mpr ⟨T.map_mem a, key a.1 hpath a.2⟩

end RegionTransport

/-- **The data of `Φ'_M` on a set of regions**, at least area without loops. -/
theorem extPhiData_of_leastArea (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlea : S.diagram.LeastArea) (hloops : S.NoLoops) {E : Finset (RegionCandidate D eps S.diagram)}
    (hE : E ⊆ S.family) : ExtPhiData S.family E where
  subset := hE
  pairwise := S.pairwise
  cell_not_mem a _ i := (a.2.innerGRegion hlea).cells_avoid _ (cell_mem S.diagram i)
  nondegenerate a ha := S.nondegenerate a (hE ha)
  noLoop a ha := hloops a (hE ha)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.map_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.exists_map_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.sideCellO_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.noLoops
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.joinsCells_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.noMultipleEdges
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.sharesEndO_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.RegionTransport.mem_linkedComponentO_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.extPhiData_of_leastArea
