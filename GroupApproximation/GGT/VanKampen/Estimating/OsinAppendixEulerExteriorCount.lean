import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExterior
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's count of `Φ'_M` with one outer vertex

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3: "By (∗), every region of it (except
possibly for the outer one) has degree at least three. Hence f ≤ 2e/3+1. By the Euler formula, we
have e ≤ v+f −2 ≤ v+2e/3−1."

For the subdivided multigraph `phiMapO family E` of
`GGT/VanKampen/Estimating/OsinAppendixEulerExterior.lean`:

* there are `4|E|` darts (`phiMapO_dartCount`);
* for a set `V` of ends containing the ends of the regions there are at most `|V| + |E|` vertices
  (`phiMapO_vertexCount_le`);
* if the regions are linked through shared ends, the map is connected and planar
  (`phiMapO_planar`), and the Euler count of a subdivided multigraph gives `|E| + 6 ≤ 3|V| + t`,
  where `t` counts the faces of degree less than six (`card_add_six_le_of_linkedO`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- **`Φ'_M` subdivided has four darts per region.** -/
theorem phiMapO_dartCount (P : ExtPhiData family E) :
    (phiMapO family E).dartCount = 4 * E.card := by
  classical
  let f : (phiMapO family E).Dart → {a // a ∈ E} × Bool × Bool :=
    fun y => (⟨phiRegionO y, phiRegionO_mem y⟩, phiSideO y, phiCellSideO y)
  have hinj : Function.Injective f := by
    intro y z h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact dartO_ext h.1 h.2.1 h.2.2
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨a, ha⟩, s, o⟩
    refine ⟨phiDartO P a ha s o, ?_⟩
    obtain ⟨hr, hs, ho⟩ := P.phiO_eq (phiDartO P a ha s o) ha (phiDartO_cross P a ha s o)
    simp only [f, hr, hs, ho]
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [CombMap.dartCount, hcard, Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := {a // a ∈ E}), Fintype.card_coe,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  ring

/-- Two end darts at the same end share a vertex of `Φ'_M`. -/
theorem ExtPhiData.vertexOf_eq_of_end (P : ExtPhiData family E) {y z : (phiMapO family E).Dart}
    (hy : phiCellSideO y = true) (hz : phiCellSideO z = true)
    (hcell : sideCellO (phiRegionO y) (phiSideO y) = sideCellO (phiRegionO z) (phiSideO z)) :
    (phiMapO family E).vertexOf y = (phiMapO family E).vertexOf z := by
  rw [phiMapO_vertexOf_eq_iff]
  have hyc := phiO_cross y
  rw [hy] at hyc
  have hzc := phiO_cross z
  rw [hz] at hzc
  have hface := P.face_not_mem_of_crossO_true hyc
  have hf := faceOf_crossO_true (phiRegionO y) hyc
  have hf' := faceOf_crossO_true (phiRegionO z) hzc
  exact collapsed_faceOf_eq_of_face_eq hface
    (hf.trans ((congrArg (endFace Delta) hcell).trans hf'.symm))

/-- Two midpoint darts of the same region share a vertex of `Φ'_M`. -/
theorem ExtPhiData.vertexOf_eq_of_midpoint (P : ExtPhiData family E)
    {y z : (phiMapO family E).Dart} (hy : phiCellSideO y = false) (hz : phiCellSideO z = false)
    (hregion : phiRegionO y = phiRegionO z) :
    (phiMapO family E).vertexOf y = (phiMapO family E).vertexOf z := by
  rw [phiMapO_vertexOf_eq_iff]
  have hyc := phiO_cross y
  rw [hy] at hyc
  have hzc := phiO_cross z
  rw [hz, ← hregion] at hzc
  have hymem := mem_cycle_crossO_false (phiRegionO y) hyc
  have hzmem := mem_cycle_crossO_false (phiRegionO y) hzc
  exact collapsed_faceOf_eq_of_mem_cycle P.pairwise (P.subset (phiRegionO_mem y)) hymem hzmem

/-- **`Φ'_M` subdivided has at most `|V| + |E|` vertices** for a set `V` of ends containing the
ends of the regions. -/
theorem phiMapO_vertexCount_le (P : ExtPhiData family E)
    (V : Finset (Option (Fin Delta.rCellCount))) (hV : ∀ a ∈ E, ∀ s : Bool, sideCellO a s ∈ V) :
    (phiMapO family E).vertexCount ≤ V.card + E.card := by
  classical
  let S := phiSubdividedMultigraphO P
  let r : (phiMapO family E).Dart → {i // i ∈ V} ⊕ {a // a ∈ E} := fun y =>
    if phiCellSideO y = true then
      Sum.inl ⟨sideCellO (phiRegionO y) (phiSideO y), hV _ (phiRegionO_mem y) _⟩
    else Sum.inr ⟨phiRegionO y, phiRegionO_mem y⟩
  have hr : ∀ y z : (phiMapO family E).Dart,
      (phiMapO family E).vertexOf y = (phiMapO family E).vertexOf z → r y = r z := by
    intro y z hyz
    have htype : (phiCellSideO y = true ↔ phiCellSideO z = true) := S.cellDart_of_vertex y z hyz
    by_cases hy : phiCellSideO y = true
    · have hz : phiCellSideO z = true := htype.mp hy
      have hend := S.endCell_of_vertex y z hy hz hyz
      simp only [r, if_pos hy, if_pos hz]
      exact congrArg Sum.inl (Subtype.ext hend)
    · have hz : ¬ phiCellSideO z = true := fun h => hy (htype.mpr h)
      have hreg := S.region_of_vertex y z hy hz hyz
      simp only [r, if_neg hy, if_neg hz]
      exact congrArg Sum.inr (Subtype.ext hreg)
  let g : (phiMapO family E).Vertex → {i // i ∈ V} ⊕ {a // a ∈ E} :=
    Quotient.lift r fun y z h => hr y z (((phiMapO family E).vertexOf_eq_iff y z).mpr h)
  have hginj : Function.Injective g := by
    intro v₁ v₂ h
    induction v₁ using Quotient.inductionOn' with
    | h y =>
    induction v₂ using Quotient.inductionOn' with
    | h z =>
    change r y = r z at h
    change (phiMapO family E).vertexOf y = (phiMapO family E).vertexOf z
    by_cases hy : phiCellSideO y = true
    · by_cases hz : phiCellSideO z = true
      · simp only [r, if_pos hy, if_pos hz, Sum.inl.injEq, Subtype.mk.injEq] at h
        exact P.vertexOf_eq_of_end hy hz h
      · simp only [r, if_pos hy, if_neg hz, reduceCtorEq] at h
    · by_cases hz : phiCellSideO z = true
      · simp only [r, if_neg hy, if_pos hz, reduceCtorEq] at h
      · simp only [r, if_neg hy, if_neg hz, Sum.inr.injEq, Subtype.mk.injEq] at h
        exact P.vertexOf_eq_of_midpoint (by simpa using hy) (by simpa using hz) h
  have hle := Nat.card_le_card_of_injective g hginj
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := {i // i ∈ V}), Fintype.card_coe,
    Nat.card_eq_fintype_card (α := {a // a ∈ E}), Fintype.card_coe] at hle
  exact hle

/-- Two selected regions share an end, a relator cell or the outer vertex. -/
def SharesEndO (E : Finset (RegionCandidate D eps Delta)) (a b : RegionCandidate D eps Delta) :
    Prop :=
  a ∈ E ∧ b ∈ E ∧ ∃ s t : Bool, sideCellO a s = sideCellO b t

/-- Every retained dart is the crossing dart named by its region, side and orientation. -/
theorem ExtPhiData.eq_phiDartO (P : ExtPhiData family E) (y : (phiMapO family E).Dart) :
    y = phiDartO P (phiRegionO y) (phiRegionO_mem y) (phiSideO y) (phiCellSideO y) := by
  obtain ⟨hr, hs, ho⟩ := P.phiO_eq (phiDartO P (phiRegionO y) (phiRegionO_mem y) (phiSideO y)
    (phiCellSideO y)) (phiRegionO_mem y) (phiDartO_cross P _ _ _ _)
  exact dartO_ext hr.symm hs.symm ho.symm

/-- Edge reversal of a crossing dart flips its orientation. -/
theorem ExtPhiData.alpha_phiDartO (P : ExtPhiData family E) (a : RegionCandidate D eps Delta)
    (ha : a ∈ E) (s o : Bool) :
    (phiMapO family E).alpha (phiDartO P a ha s o) = phiDartO P a ha s (!o) := by
  have h := (crossO_alpha a s o (phiDartO P a ha s o).1.1).mpr (phiDartO_cross P a ha s o)
  obtain ⟨hr, hs, ho⟩ := P.phiO_eq ((phiMapO family E).alpha (phiDartO P a ha s o)) ha h
  obtain ⟨hr', hs', ho'⟩ := P.phiO_eq (phiDartO P a ha s (!o)) ha (phiDartO_cross P a ha s (!o))
  exact dartO_ext (hr.trans hr'.symm) (hs.trans hs'.symm) (ho.trans ho'.symm)

/-- The four crossing darts of a region are connected to its source end dart. -/
theorem ExtPhiData.connected_phiDartO (P : ExtPhiData family E) (a : RegionCandidate D eps Delta)
    (ha : a ∈ E) (s o : Bool) :
    Relation.EqvGen (phiMapO family E).Adjacent (phiDartO P a ha true true)
      (phiDartO P a ha s o) := by
  have halpha : ∀ s o : Bool, Relation.EqvGen (phiMapO family E).Adjacent
      (phiDartO P a ha s o) (phiDartO P a ha s (!o)) := by
    intro s o
    exact Relation.EqvGen.rel _ _ (Or.inl (P.alpha_phiDartO a ha s o))
  have hmid : Relation.EqvGen (phiMapO family E).Adjacent
      (phiDartO P a ha true false) (phiDartO P a ha false false) := by
    apply CombMap.eqvGen_of_sameCycle_sigma
    rw [← CombMap.vertexOf_eq_iff]
    obtain ⟨hr, -, ho⟩ := P.phiO_eq (phiDartO P a ha true false) ha (phiDartO_cross P _ _ _ _)
    obtain ⟨hr', -, ho'⟩ := P.phiO_eq (phiDartO P a ha false false) ha (phiDartO_cross P _ _ _ _)
    exact P.vertexOf_eq_of_midpoint ho ho' (hr.trans hr'.symm)
  cases s <;> cases o
  · -- false false
    exact Relation.EqvGen.trans _ _ _ (halpha true true) hmid
  · -- false true
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ (halpha true true) hmid)
      (halpha false false)
  · -- true false
    exact halpha true true
  · exact Relation.EqvGen.refl _

/-- **`Φ'_M` subdivided is connected when the regions are linked through shared ends.** -/
theorem phiMapO_connected (P : ExtPhiData family E)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesEndO E) a b) :
    (phiMapO family E).IsConnected := by
  have hbase : ∀ y : (phiMapO family E).Dart, Relation.EqvGen (phiMapO family E).Adjacent
      (phiDartO P (phiRegionO y) (phiRegionO_mem y) true true) y := by
    intro y
    have h := P.connected_phiDartO (phiRegionO y) (phiRegionO_mem y) (phiSideO y)
      (phiCellSideO y)
    rwa [← P.eq_phiDartO y] at h
  have hstep : ∀ a b, SharesEndO E a b → ∀ (ha : a ∈ E) (hb : b ∈ E),
      Relation.EqvGen (phiMapO family E).Adjacent (phiDartO P a ha true true)
        (phiDartO P b hb true true) := by
    rintro a b ⟨-, -, s, t, hst⟩ ha hb
    have hcellEq : Relation.EqvGen (phiMapO family E).Adjacent
        (phiDartO P a ha s true) (phiDartO P b hb t true) := by
      apply CombMap.eqvGen_of_sameCycle_sigma
      rw [← CombMap.vertexOf_eq_iff]
      obtain ⟨hr, hs, ho⟩ := P.phiO_eq (phiDartO P a ha s true) ha (phiDartO_cross P _ _ _ _)
      obtain ⟨hr', hs', ho'⟩ := P.phiO_eq (phiDartO P b hb t true) hb (phiDartO_cross P _ _ _ _)
      exact P.vertexOf_eq_of_end ho ho' (by rw [hr, hs, hr', hs']; exact hst)
    exact Relation.EqvGen.trans _ _ _ (P.connected_phiDartO a ha s true)
      (Relation.EqvGen.trans _ _ _ hcellEq
        (Relation.EqvGen.symm _ _ (P.connected_phiDartO b hb t true)))
  have hlink : ∀ a b, Relation.ReflTransGen (SharesEndO E) a b → ∀ (ha : a ∈ E) (hb : b ∈ E),
      Relation.EqvGen (phiMapO family E).Adjacent (phiDartO P a ha true true)
        (phiDartO P b hb true true) := by
    intro a b h
    induction h with
    | refl => intro ha hb; exact Relation.EqvGen.refl _
    | tail _ hbc ih =>
        intro ha hc
        exact Relation.EqvGen.trans _ _ _ (ih ha hbc.1) (hstep _ _ hbc hbc.1 hc)
  intro y z
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hbase y))
    (Relation.EqvGen.trans _ _ _
      (hlink _ _ (hlinked _ (phiRegionO_mem y) _ (phiRegionO_mem z)) (phiRegionO_mem y)
        (phiRegionO_mem z)) (hbase z))

/-- **`Φ'_M` subdivided is planar** when the regions are linked and at least one is selected. -/
theorem phiMapO_planar (P : ExtPhiData family E)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesEndO E) a b)
    {a : RegionCandidate D eps Delta} (ha : a ∈ E) : (phiMapO family E).IsPlanar :=
  (phiMapO_isRestriction family E).planar
    (CombMap.dual_planar _ (collapsedMap_planar P.pairwise (phiDartO P a ha true true).1))
    (phiMapO_connected P hlinked) (phiDartO P a ha true true)

/-- **Euler's count of `Φ'_M` for linked regions**: `|E| + 6 ≤ 3|V| + t` for a set `V` of ends
containing the ends of the regions, where `t` counts the faces of degree less than six. -/
theorem card_add_six_le_of_linkedO (P : ExtPhiData family E)
    (V : Finset (Option (Fin Delta.rCellCount))) (hV : ∀ a ∈ E, ∀ s : Bool, sideCellO a s ∈ V)
    (hne : E.Nonempty)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesEndO E) a b) :
    E.card + 6 ≤ 3 * V.card + (Finset.univ.filter fun f : (phiMapO family E).Face =>
      (phiMapO family E).faceDegree f < 6).card := by
  obtain ⟨a, ha⟩ := hne
  exact CombMap.edgeBound_of_subdividedMultigraph (phiSubdividedMultigraphO P)
    (phiMapO_planar P hlinked ha) (phiMapO_dartCount P) (phiMapO_vertexCount_le P V hV)

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMapO_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMapO_vertexCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMapO_connected
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMapO_planar
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.card_add_six_le_of_linkedO
