import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiBound
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInterior
import GroupApproximation.Meta.AxiomGuard

/-!
# The hereditary Euler bound of `Φ_M`

For regions satisfying `PhiData` and a cell set `V` containing all their ends, `|E| ≤ 3(|V| − 1)`
(`card_le_of_endpoints`): split `E` into the regions linked to one region through shared cells and
the rest, whose end cells are disjoint, and apply `card_le_of_linked` to a linked set.  Reading an
endpoint-closed state of Osin's incidence graph as such a set gives the corrected hereditary planar
edge bound `HasEndpointClosedPlanarEdgeBound (InteriorEdge.Incident (selected := family))`
(`hasEndpointClosedPlanarEdgeBound_of_phiData`), the graph content of Osin's condition `(∗)`.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

open Equiv
universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)}

theorem PhiData.mono (P : PhiData family E) {E' : Finset (RegionCandidate D eps Delta)}
    (h : E' ⊆ E) : PhiData family E' where
  subset := h.trans P.subset
  pairwise := P.pairwise
  cell_not_mem := P.cell_not_mem
  interior a ha := P.interior a (h ha)
  nondegenerate a ha := P.nondegenerate a (h ha)
  noLoop a ha := P.noLoop a (h ha)
  noMultiple a ha b hb hab := P.noMultiple a (h ha) b (h hb) hab

theorem sharesCell_symm {a b : RegionCandidate D eps Delta} (h : SharesCell E a b) :
    SharesCell E b a := by
  obtain ⟨ha, hb, s, t, hst⟩ := h
  exact ⟨hb, ha, t, s, hst.symm⟩

theorem linked_symm {a b : RegionCandidate D eps Delta}
    (h : Relation.ReflTransGen (SharesCell E) a b) : Relation.ReflTransGen (SharesCell E) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (sharesCell_symm hbc) ih

/-- The end cells of a set of regions. -/
noncomputable def endCells (E : Finset (RegionCandidate D eps Delta)) :
    Finset (Fin Delta.rCellCount) := by
  classical
  exact E.biUnion fun a => {sideCell a true, sideCell a false}

theorem sideCell_mem_endCells {a : RegionCandidate D eps Delta} (ha : a ∈ E) (s : Bool) :
    sideCell a s ∈ endCells E := by
  classical
  simp only [endCells, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨a, ha, by cases s <;> simp⟩

/-- **The Euler count of `Φ_M` on any set of regions**, through linked components. -/
theorem card_le_of_endpoints (P : PhiData family E) (V : Finset (Fin Delta.rCellCount))
    (hV : ∀ a ∈ E, ∀ s : Bool, sideCell a s ∈ V) (hVne : V.Nonempty) :
    E.card ≤ 3 * (V.card - 1) := by
  classical
  induction E using Finset.strongInductionOn generalizing V with
  | _ E ih =>
      by_cases hE : E.Nonempty
      · obtain ⟨a₀, ha₀⟩ := hE
        let C := E.filter fun b => Relation.ReflTransGen (SharesCell E) a₀ b
        let R := E.filter fun b => ¬ Relation.ReflTransGen (SharesCell E) a₀ b
        have hcard : C.card + R.card = E.card := Finset.card_filter_add_card_filter_not _
        by_cases hR : R = ∅
        · -- all regions are linked
          have hall : ∀ b ∈ E, Relation.ReflTransGen (SharesCell E) a₀ b := by
            intro b hb
            by_contra hnot
            have : b ∈ R := Finset.mem_filter.mpr ⟨hb, hnot⟩
            rw [hR] at this
            exact absurd this (Finset.notMem_empty b)
          exact card_le_of_linked P V hV ⟨a₀, ha₀⟩ fun a ha b hb =>
            (linked_symm (hall a ha)).trans (hall b hb)
        · -- two proper parts with disjoint end cells
          have hCsub : C ⊆ E := Finset.filter_subset _ _
          have hRsub : R ⊆ E := Finset.filter_subset _ _
          have ha₀C : a₀ ∈ C := Finset.mem_filter.mpr ⟨ha₀, Relation.ReflTransGen.refl⟩
          obtain ⟨b₀, hb₀⟩ := Finset.nonempty_iff_ne_empty.mpr hR
          have hCss : C ⊂ E := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hCsub, ?_⟩
            intro hCE
            have hb₀E := hRsub hb₀
            rw [← hCE] at hb₀E
            exact (Finset.mem_filter.mp hb₀).2 (Finset.mem_filter.mp hb₀E).2
          have hRss : R ⊂ E := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hRsub, ?_⟩
            intro hRE
            have ha₀R : a₀ ∈ R := by rw [hRE]; exact ha₀
            exact (Finset.mem_filter.mp ha₀R).2 Relation.ReflTransGen.refl
          have hIC := ih C hCss (P.mono hCsub) (endCells C) (fun a ha s => sideCell_mem_endCells ha s)
            ⟨_, sideCell_mem_endCells ha₀C true⟩
          have hIR := ih R hRss (P.mono hRsub) (endCells R) (fun a ha s => sideCell_mem_endCells ha s)
            ⟨_, sideCell_mem_endCells hb₀ true⟩
          have hdisj : endCells C ∩ endCells R = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro i hi
            obtain ⟨hiC, hiR⟩ := Finset.mem_inter.mp hi
            simp only [endCells, Finset.mem_biUnion, Finset.mem_insert,
              Finset.mem_singleton] at hiC hiR
            obtain ⟨a, haC, has⟩ := hiC
            obtain ⟨b, hbR, hbs⟩ := hiR
            have hab : SharesCell E a b := by
              refine ⟨hCsub haC, hRsub hbR, ?_⟩
              rcases has with has | has <;> rcases hbs with hbs | hbs
              · exact ⟨true, true, has.symm.trans hbs⟩
              · exact ⟨true, false, has.symm.trans hbs⟩
              · exact ⟨false, true, has.symm.trans hbs⟩
              · exact ⟨false, false, has.symm.trans hbs⟩
            exact (Finset.mem_filter.mp hbR).2
              ((Finset.mem_filter.mp haC).2.tail hab)
          have hunion : endCells C ∪ endCells R ⊆ V := by
            intro i hi
            rcases Finset.mem_union.mp hi with hi | hi
            · simp only [endCells, Finset.mem_biUnion, Finset.mem_insert,
                Finset.mem_singleton] at hi
              obtain ⟨a, ha, has⟩ := hi
              rcases has with rfl | rfl
              · exact hV a (hCsub ha) true
              · exact hV a (hCsub ha) false
            · simp only [endCells, Finset.mem_biUnion, Finset.mem_insert,
                Finset.mem_singleton] at hi
              obtain ⟨a, ha, has⟩ := hi
              rcases has with rfl | rfl
              · exact hV a (hRsub ha) true
              · exact hV a (hRsub ha) false
          have hsum := Finset.card_union_add_card_inter (endCells C) (endCells R)
          rw [hdisj, Finset.card_empty, add_zero] at hsum
          have hle := Finset.card_le_card hunion
          have hCpos : 0 < (endCells C).card :=
            Finset.card_pos.mpr ⟨_, sideCell_mem_endCells ha₀C true⟩
          have hRpos : 0 < (endCells R).card :=
            Finset.card_pos.mpr ⟨_, sideCell_mem_endCells hb₀ true⟩
          omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hE
        simp [hE]

/-- **The corrected hereditary planar edge bound of `Φ_M`.** -/
theorem hasEndpointClosedPlanarEdgeBound_of_phiData
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    (hcell : ∀ a ∈ family, ∀ i : Fin Delta.rCellCount, (cell Delta i).face ∉ a.1)
    (hnondeg : ∀ a ∈ family, 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length)
    (hloop : ∀ a ∈ family, a.2.target ≠ some a.2.source)
    (hmulti : ∀ a ∈ family, ∀ b ∈ family, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      ((a.2.source = i ∧ a.2.target = some j) ∨ (a.2.source = j ∧ a.2.target = some i)) →
      ((b.2.source = i ∧ b.2.target = some j) ∨ (b.2.source = j ∧ b.2.target = some i)) → False)
    [DecidableEq (Fin Delta.rCellCount)] [DecidableEq (InteriorEdge family)]
    [DecidableRel (InteriorEdge.Incident (selected := family))] :
    HasEndpointClosedPlanarEdgeBound (InteriorEdge.Incident (selected := family)) := by
  classical
  intro vertices edges _hcovered hclosed hne
  let E : Finset (RegionCandidate D eps Delta) :=
    edges.map ⟨Subtype.val, Subtype.val_injective⟩
  have hEsub : ∀ a ∈ E, a ∈ ofKind family true := by
    intro a ha
    obtain ⟨e, -, rfl⟩ := Finset.mem_map.mp ha
    exact e.2
  have hEfam : ∀ a ∈ E, a ∈ family := fun a ha => (Finset.mem_filter.mp (hEsub a ha)).1
  have P : PhiData family E :=
    { subset := fun a ha => hEfam a ha
      pairwise := hpairwise
      cell_not_mem := hcell
      interior := fun a ha => (Finset.mem_filter.mp (hEsub a ha)).2
      nondegenerate := fun a ha => hnondeg a (hEfam a ha)
      noLoop := fun a ha => hloop a (hEfam a ha)
      noMultiple := fun a ha b hb hab => hmulti a (hEfam a ha) b (hEfam b hb) hab }
  have hV : ∀ a ∈ E, ∀ s : Bool, sideCell a s ∈ vertices := by
    intro a ha s
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp ha
    apply hclosed e he
    cases s with
    | true => exact Or.inl rfl
    | false =>
        right
        obtain ⟨j, hj⟩ := InteriorEdge.exists_target (selected := family) e
        simp [sideCell, hj]
  have hbound := card_le_of_endpoints P vertices hV hne
  rwa [Finset.card_map] at hbound

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.linked_symm
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.card_le_of_endpoints
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.hasEndpointClosedPlanarEdgeBound_of_phiData
