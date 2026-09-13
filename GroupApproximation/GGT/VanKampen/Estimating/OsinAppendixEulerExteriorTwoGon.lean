import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExterior
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-gons of `Φ'_M` with one outer vertex

Osin, arXiv:math/0411039v3, Appendix, before Lemma 9.3: "For any distinguished system of
ε-contiguity subdiagrams `M` in `∆`, the graph `Φ_M` is simple and inside every 2-gon of
`Φ'_M`, there is a vertex of `Φ_M`."

A two-gon of the subdivided multigraph `phiMapO family E`
(`GGT/VanKampen/Estimating/OsinAppendixEulerExterior.lean`) is a face through a cell dart that
closes after four steps and crosses two different regions (kh-ejz's `IsTwoGon`).  Around such a
face the far end of each region is the near end of the other.  When no two regions join the same
two cells, both regions join one cell to the outer vertex.

* `sideCellO_facePerm_facePerm`: two steps around a face from a cell dart reach the far end of
  its region;
* `exterior_of_sideCellO_eq`: two different regions with swapped ends, and no multiple edge
  between cells, are exterior regions of one cell;
* `exterior_of_isTwoGon`: the two regions of a two-gon are different exterior regions of one
  cell.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- Edge reversal keeps the region and the side of a retained dart and flips its orientation. -/
theorem ExtPhiData.phiO_alpha (P : ExtPhiData family E) (y : (phiMapO family E).Dart) :
    phiRegionO ((phiMapO family E).alpha y) = phiRegionO y ∧
      phiSideO ((phiMapO family E).alpha y) = phiSideO y ∧
        phiCellSideO ((phiMapO family E).alpha y) = !phiCellSideO y :=
  P.phiO_eq ((phiMapO family E).alpha y) (phiRegionO_mem y)
    ((crossO_alpha (phiRegionO y) (phiSideO y) (phiCellSideO y) y.1.1).mpr (phiO_cross y))

/-- Rotation keeps the orientation of a retained dart. -/
theorem ExtPhiData.phiCellSideO_sigma (P : ExtPhiData family E) (y : (phiMapO family E).Dart) :
    phiCellSideO ((phiMapO family E).sigma y) = phiCellSideO y := by
  have h := (phiSubdividedMultigraphO P).cellDart_sigma y
  change phiCellSideO ((phiMapO family E).sigma y) = true ↔ phiCellSideO y = true at h
  revert h
  cases phiCellSideO ((phiMapO family E).sigma y) <;> cases phiCellSideO y <;> decide

/-- Rotation at a midpoint keeps the region and swaps the side. -/
theorem ExtPhiData.phiO_sigma_of_midpoint (P : ExtPhiData family E)
    (y : (phiMapO family E).Dart) (hy : phiCellSideO y = false) :
    phiRegionO ((phiMapO family E).sigma y) = phiRegionO y ∧
      phiSideO ((phiMapO family E).sigma y) = !phiSideO y := by
  have hy' : ¬ (phiSubdividedMultigraphO P).IsCellDart y := by
    change ¬ phiCellSideO y = true
    simp [hy]
  have hreg : phiRegionO ((phiMapO family E).sigma y) = phiRegionO y :=
    (phiSubdividedMultigraphO P).region_sigma y hy'
  have hne : (phiMapO family E).sigma y ≠ y :=
    (phiSubdividedMultigraphO P).sigma_ne_of_midpoint y hy'
  have hside : phiSideO ((phiMapO family E).sigma y) ≠ phiSideO y := fun hs =>
    hne (dartO_ext hreg hs (P.phiCellSideO_sigma y))
  refine ⟨hreg, ?_⟩
  revert hside
  cases phiSideO ((phiMapO family E).sigma y) <;> cases phiSideO y <;> decide

/-- **Two steps around a face from a cell dart reach the far end of its region.** -/
theorem sideCellO_facePerm_facePerm (P : ExtPhiData family E)
    (y : (phiMapO family E).Dart) (hy : phiCellSideO y = true) :
    phiCellSideO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) = true ∧
      sideCellO (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))
          (phiSideO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) =
        sideCellO (phiRegionO y) (!phiSideO y) := by
  obtain ⟨hr1, hs1, hc1⟩ := P.phiO_alpha y
  have hc1' : phiCellSideO ((phiMapO family E).alpha y) = false := by simp [hc1, hy]
  obtain ⟨hr2, hs2⟩ := P.phiO_sigma_of_midpoint ((phiMapO family E).alpha y) hc1'
  have hc2 : phiCellSideO ((phiMapO family E).facePerm y) = false :=
    (P.phiCellSideO_sigma ((phiMapO family E).alpha y)).trans hc1'
  have hr : phiRegionO ((phiMapO family E).facePerm y) = phiRegionO y := hr2.trans hr1
  have hs : phiSideO ((phiMapO family E).facePerm y) = !phiSideO y := hs2.trans (congrArg not hs1)
  obtain ⟨hr3, hs3, hc3⟩ := P.phiO_alpha ((phiMapO family E).facePerm y)
  have hc3' : phiCellSideO ((phiMapO family E).alpha ((phiMapO family E).facePerm y)) = true := by
    simp [hc3, hc2]
  have hend := (phiSubdividedMultigraphO P).endCell_sigma
    ((phiMapO family E).alpha ((phiMapO family E).facePerm y)) hc3'
  change sideCellO (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))
      (phiSideO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) =
    sideCellO (phiRegionO ((phiMapO family E).alpha ((phiMapO family E).facePerm y)))
      (phiSideO ((phiMapO family E).alpha ((phiMapO family E).facePerm y))) at hend
  refine ⟨(P.phiCellSideO_sigma ((phiMapO family E).alpha ((phiMapO family E).facePerm y))).trans
    hc3', ?_⟩
  rw [hend, hr3, hs3, hr, hs]

/-- **Two different regions with swapped ends are exterior regions of one cell**, when no two
regions join the same two cells. -/
theorem exterior_of_sideCellO_eq
    (hmulti : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False)
    {a b : RegionCandidate D eps Delta} (ha : a ∈ E) (hb : b ∈ E) (hab : b ≠ a) {s t : Bool}
    (h1 : sideCellO b t = sideCellO a (!s)) (h2 : sideCellO a s = sideCellO b (!t)) :
    a.2.target = none ∧ b.2.target = none ∧ b.2.source = a.2.source := by
  have hab' : a ≠ b := fun h => hab h.symm
  cases s <;> cases t
  · change b.2.target = some a.2.source at h1
    change a.2.target = some b.2.source at h2
    exact (hmulti a ha b hb hab' a.2.source b.2.source (Or.inl ⟨rfl, h2⟩)
      (Or.inr ⟨rfl, h1⟩)).elim
  · change some b.2.source = some a.2.source at h1
    change a.2.target = b.2.target at h2
    rcases Option.eq_none_or_eq_some a.2.target with hat | ⟨j, hat⟩
    · exact ⟨hat, h2.symm.trans hat, Option.some.inj h1⟩
    · exact (hmulti a ha b hb hab' a.2.source j (Or.inl ⟨rfl, hat⟩)
        (Or.inl ⟨Option.some.inj h1, h2.symm.trans hat⟩)).elim
  · change b.2.target = a.2.target at h1
    change some a.2.source = some b.2.source at h2
    rcases Option.eq_none_or_eq_some a.2.target with hat | ⟨j, hat⟩
    · exact ⟨hat, h1.trans hat, (Option.some.inj h2).symm⟩
    · exact (hmulti a ha b hb hab' a.2.source j (Or.inl ⟨rfl, hat⟩)
        (Or.inl ⟨(Option.some.inj h2).symm, h1.trans hat⟩)).elim
  · change some b.2.source = a.2.target at h1
    change some a.2.source = b.2.target at h2
    exact (hmulti a ha b hb hab' a.2.source b.2.source (Or.inl ⟨rfl, h1.symm⟩)
      (Or.inr ⟨rfl, h2.symm⟩)).elim

/-- **The two regions of a two-gon of `Φ'_M` are different exterior regions of one cell**, when
no two regions join the same two cells, the half "`Φ_M` is simple" of `(∗)`. -/
theorem exterior_of_isTwoGon (P : ExtPhiData family E)
    (hmulti : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False)
    {f : (phiMapO family E).Face} (hf : (phiSubdividedMultigraphO P).IsTwoGon f) :
    ∃ d : (phiMapO family E).Dart, phiCellSideO d = true ∧ (phiMapO family E).faceOf d = f ∧
      phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm d)) ≠ phiRegionO d ∧
        (phiRegionO d).2.target = none ∧
          (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm d))).2.target =
            none ∧
          (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm d))).2.source =
            (phiRegionO d).2.source := by
  obtain ⟨d, hd, hface, h4, hR⟩ := hf
  have hdc : phiCellSideO d = true := hd
  obtain ⟨hd2, h1⟩ := sideCellO_facePerm_facePerm P d hdc
  obtain ⟨-, h2⟩ := sideCellO_facePerm_facePerm P _ hd2
  rw [h4] at h2
  exact ⟨d, hdc, hface, hR, exterior_of_sideCellO_eq hmulti (phiRegionO_mem d)
    (phiRegionO_mem ((phiMapO family E).facePerm ((phiMapO family E).facePerm d))) hR h1 h2⟩

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sideCellO_facePerm_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exterior_of_sideCellO_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exterior_of_isTwoGon
