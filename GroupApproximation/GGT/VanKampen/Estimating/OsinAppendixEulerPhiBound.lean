import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler bound of `Φ_M` for linked regions

If the selected regions are linked to each other through shared end cells, the subdivided graph
`phiMap family E` is connected (`phiMap_connected`), hence a planar restriction of the dual of the
collapsed diagram (`phiMap_planar`), and Euler's count gives `|E| ≤ 3(|V| − 1)` for any cell set `V`
containing the ends of the regions (`card_le_of_linked`).
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

/-- Two selected regions share an end cell. -/
def SharesCell (E : Finset (RegionCandidate D eps Delta)) (a b : RegionCandidate D eps Delta) :
    Prop :=
  a ∈ E ∧ b ∈ E ∧ ∃ s t : Bool, sideCell a s = sideCell b t

/-- Every retained dart is the crossing dart named by its region, side and orientation. -/
theorem PhiData.eq_phiDart (P : PhiData family E) (y : (phiMap family E).Dart) :
    y = phiDart P (phiRegion y) (phiRegion_mem y) (phiSide y) (phiCellSide y) := by
  obtain ⟨hr, hs, ho⟩ := P.phi_eq (phiDart P (phiRegion y) (phiRegion_mem y) (phiSide y)
    (phiCellSide y)) (phiRegion_mem y) (phiDart_cross P _ _ _ _)
  exact dart_ext hr.symm hs.symm ho.symm

/-- Edge reversal of a crossing dart flips its orientation. -/
theorem PhiData.alpha_phiDart (P : PhiData family E) (a : RegionCandidate D eps Delta)
    (ha : a ∈ E) (s o : Bool) :
    (phiMap family E).alpha (phiDart P a ha s o) = phiDart P a ha s (!o) := by
  have h := (cross_alpha a s o (phiDart P a ha s o).1.1).mpr (phiDart_cross P a ha s o)
  obtain ⟨hr, hs, ho⟩ := P.phi_eq ((phiMap family E).alpha (phiDart P a ha s o)) ha h
  obtain ⟨hr', hs', ho'⟩ := P.phi_eq (phiDart P a ha s (!o)) ha (phiDart_cross P a ha s (!o))
  exact dart_ext (hr.trans hr'.symm) (hs.trans hs'.symm) (ho.trans ho'.symm)

/-- The four crossing darts of a region are connected to its source cell dart. -/
theorem PhiData.connected_phiDart (P : PhiData family E) (a : RegionCandidate D eps Delta)
    (ha : a ∈ E) (s o : Bool) :
    Relation.EqvGen (phiMap family E).Adjacent (phiDart P a ha true true) (phiDart P a ha s o) := by
  have halpha : ∀ s o : Bool, Relation.EqvGen (phiMap family E).Adjacent
      (phiDart P a ha s o) (phiDart P a ha s (!o)) := by
    intro s o
    exact Relation.EqvGen.rel _ _ (Or.inl (P.alpha_phiDart a ha s o))
  have hmid : Relation.EqvGen (phiMap family E).Adjacent
      (phiDart P a ha true false) (phiDart P a ha false false) := by
    apply CombMap.eqvGen_of_sameCycle_sigma
    rw [← CombMap.vertexOf_eq_iff]
    obtain ⟨hr, -, ho⟩ := P.phi_eq (phiDart P a ha true false) ha (phiDart_cross P _ _ _ _)
    obtain ⟨hr', -, ho'⟩ := P.phi_eq (phiDart P a ha false false) ha (phiDart_cross P _ _ _ _)
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

/-- **`Φ_M` subdivided is connected when the regions are linked through shared cells.** -/
theorem phiMap_connected (P : PhiData family E)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesCell E) a b) :
    (phiMap family E).IsConnected := by
  have hbase : ∀ y : (phiMap family E).Dart, Relation.EqvGen (phiMap family E).Adjacent
      (phiDart P (phiRegion y) (phiRegion_mem y) true true) y := by
    intro y
    have h := P.connected_phiDart (phiRegion y) (phiRegion_mem y) (phiSide y) (phiCellSide y)
    rwa [← P.eq_phiDart y] at h
  have hstep : ∀ a b, SharesCell E a b → ∀ (ha : a ∈ E) (hb : b ∈ E),
      Relation.EqvGen (phiMap family E).Adjacent (phiDart P a ha true true)
        (phiDart P b hb true true) := by
    rintro a b ⟨-, -, s, t, hst⟩ ha hb
    have hcellEq : Relation.EqvGen (phiMap family E).Adjacent
        (phiDart P a ha s true) (phiDart P b hb t true) := by
      apply CombMap.eqvGen_of_sameCycle_sigma
      rw [← CombMap.vertexOf_eq_iff]
      obtain ⟨hr, hs, ho⟩ := P.phi_eq (phiDart P a ha s true) ha (phiDart_cross P _ _ _ _)
      obtain ⟨hr', hs', ho'⟩ := P.phi_eq (phiDart P b hb t true) hb (phiDart_cross P _ _ _ _)
      exact P.vertexOf_eq_of_cell ho ho' (by rw [hr, hs, hr', hs']; exact hst)
    exact Relation.EqvGen.trans _ _ _ (P.connected_phiDart a ha s true)
      (Relation.EqvGen.trans _ _ _ hcellEq
        (Relation.EqvGen.symm _ _ (P.connected_phiDart b hb t true)))
  have hlink : ∀ a b, Relation.ReflTransGen (SharesCell E) a b → ∀ (ha : a ∈ E) (hb : b ∈ E),
      Relation.EqvGen (phiMap family E).Adjacent (phiDart P a ha true true)
        (phiDart P b hb true true) := by
    intro a b h
    induction h with
    | refl => intro ha hb; exact Relation.EqvGen.refl _
    | tail _ hbc ih =>
        intro ha hc
        exact Relation.EqvGen.trans _ _ _ (ih ha hbc.1) (hstep _ _ hbc hbc.1 hc)
  intro y z
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hbase y))
    (Relation.EqvGen.trans _ _ _
      (hlink _ _ (hlinked _ (phiRegion_mem y) _ (phiRegion_mem z)) (phiRegion_mem y)
        (phiRegion_mem z)) (hbase z))

/-- **`Φ_M` subdivided is planar** when the regions are linked and at least one is selected. -/
theorem phiMap_planar (P : PhiData family E)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesCell E) a b)
    {a : RegionCandidate D eps Delta} (ha : a ∈ E) : (phiMap family E).IsPlanar :=
  (phiMap_isRestriction family E).planar
    (CombMap.dual_planar _ (collapsedMap_planar P.pairwise (phiDart P a ha true true).1))
    (phiMap_connected P hlinked) (phiDart P a ha true true)

/-- **Euler's count of `Φ_M` for linked regions**: `|E| ≤ 3(|V| − 1)` for a cell set `V` containing
the ends of the regions. -/
theorem card_le_of_linked (P : PhiData family E) (V : Finset (Fin Delta.rCellCount))
    (hV : ∀ a ∈ E, ∀ s : Bool, sideCell a s ∈ V) (hne : E.Nonempty)
    (hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesCell E) a b) :
    E.card ≤ 3 * (V.card - 1) := by
  classical
  obtain ⟨a, ha⟩ := hne
  have hc : 2 ≤ V.card := by
    have hsub : ({sideCell a true, sideCell a false} : Finset (Fin Delta.rCellCount)) ⊆ V := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hV a ha true
      · exact hV a ha false
    have hpair : ({sideCell a true, sideCell a false} : Finset (Fin Delta.rCellCount)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr (P.sideCell_ne ha)
    exact hpair ▸ Finset.card_le_card hsub
  exact CombMap.edgeBound_of_subdividedGraph (phiMap family E) (phiSubdividedGraph P)
    (phiMap_planar P hlinked ha) hc (phiMap_dartCount P) (phiMap_vertexCount_le P V hV)

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.PhiData.eq_phiDart
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.PhiData.connected_phiDart
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMap_connected
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.phiMap_planar
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.card_le_of_linked
