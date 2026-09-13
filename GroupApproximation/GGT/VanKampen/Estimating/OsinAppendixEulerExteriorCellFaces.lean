import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorLinked
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorTwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerHereditary
import GroupApproximation.GGT.VanKampen.CombMapRestrictionFaceClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces of `Φ'_M` that hold a relator cell

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "For any distinguished
system of ε-contiguity subdiagrams `M` in `∆`, the graph `Φ_M` is simple and inside every 2-gon of
`Φ'_M`, there is a vertex of `Φ_M`."  With the vertices `O_i` merged into one outer vertex `O`
(`Estimating/OsinAppendixEulerExterior.lean`), a two-gon of `Φ'_M` holds a corner of the sections
in its gap at `O` (C4 of the Lemma 9.3 count), holds a vertex of `Φ_M` (C5, this module), or is
empty (C6, `EmptyTwoGonInput`).

Take the regions `C = linkedComponentO E a₀` linked to an exterior region `a₀`, and their graph
`phiMapO family C`.  A face of it **holds a relator cell** (`RegionCandidate.HoldsCellO`) when its
face class reaches a dart of a relator cell that is not an end of `C`.  The face class advances
around the faces of the dual of the collapsed map and crosses the edges that are not retained
(`CombMap.FaceClassStep`, `GGT/VanKampen/CombMapRestrictionFaceClasses.lean`).

`CellFaceCountInput` states C5 as a count, and `cellFaceCountInput` proves it:

  `|E| + 3 · #{faces holding a cell} ≤ |C| + 3 · #{relator cells that are not ends of C}`.

By `CombMap.IsRestriction.faceOf_eq_of_faceClass` two different faces hold disjoint sets of cells.
A region outside `C` has both ends among the cells held by one face, and `card_le_of_endpoints`
bounds the regions on the cells `X` held by one face by `3(|X| − 1)`.  With the Euler count
`card_add_six_le_linkedComponentO`, `|C| + 6 ≤ 3(1 + #{ends of C}) + t`, and
`t ≤ r + #{faces holding a cell}` from C3, C4 and C6, the count gives `|E| ≤ 3(n + r − 1)`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

namespace Embedded.RegionCandidate

/-- **A face of `Φ'_M` holds a relator cell** that is not an end of the selected regions `E`: from
a retained dart of the face, advancing around the faces of the dual of the collapsed map and
crossing edges that are not retained reaches a dart of the cell. -/
def HoldsCellO {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (family E : Finset (RegionCandidate D eps Delta))
    (f : (phiMapO family E).Face) : Prop :=
  ∃ i : Fin Delta.rCellCount, some i ∉ endCellsO E ∧
    ∃ d : (phiMapO family E).Dart, (phiMapO family E).faceOf d = f ∧
      ∃ x : (collapsedMap family).dual.Dart,
        Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E))
          d.1 x ∧ Delta.toCombMap.faceOf x.1 = (cell Delta i).face

end Embedded.RegionCandidate

open scoped Classical in
/-- **C5 of Osin's Lemma 9.3: the faces of `Φ'_M` that hold a relator cell.**  Take regions `E`
carrying the data of `Φ'_M`, no two of them joining the same two cells, and an exterior region
`a₀ ∈ E` with its component `C = linkedComponentO E a₀`.  Then `|E|`, plus three for each face of
`phiMapO family C` that holds a relator cell, is at most `|C|` plus three times the number of
relator cells that are not ends of `C`. -/
def CellFaceCountInput (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (family E : Finset (RegionCandidate D eps Delta)),
    RegionCandidate.ExtPhiData family E →
    (∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False) →
    ∀ a₀ ∈ E, a₀.2.target = none →
      E.card +
          3 * (Finset.univ.filter fun f :
            (RegionCandidate.phiMapO family (RegionCandidate.linkedComponentO E a₀)).Face =>
              RegionCandidate.HoldsCellO family (RegionCandidate.linkedComponentO E a₀) f).card ≤
        (RegionCandidate.linkedComponentO E a₀).card +
          3 * (Finset.univ.filter fun i : Fin Delta.rCellCount =>
            some i ∉ RegionCandidate.endCellsO (RegionCandidate.linkedComponentO E a₀)).card

namespace Embedded.RegionCandidate

variable {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {family E : Finset (RegionCandidate D eps Delta)}

/-- A face class for a predicate is a face class for the range of its subtype embedding. -/
theorem eqvGen_faceClassStep_range {M : CombMap.{v}} {keep : M.Dart → Prop} {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M keep) x y) :
    Relation.EqvGen
      (CombMap.FaceClassStep M (· ∈ Set.range (Function.Embedding.subtype keep))) x y := by
  induction h with
  | rel _ _ hx =>
      refine Relation.EqvGen.rel _ _ ?_
      rcases hx with hx | ⟨hnot, hx⟩
      · exact Or.inl hx
      · refine Or.inr ⟨?_, hx⟩
        rintro ⟨z, rfl⟩
        exact hnot z.2
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Across a dart that is not retained and around the next face, a face class of the dual advances
along a face of the map. -/
theorem eqvGen_facePerm_of_not_keep {M : CombMap.{v}} {keep : M.dual.Dart → Prop}
    {x : M.dual.Dart} (hx : ¬ keep x) :
    Relation.EqvGen (CombMap.FaceClassStep M.dual keep) x (M.facePerm x) := by
  have hface : M.facePerm x = M.dual.facePerm (M.dual.alpha x) := by
    change M.facePerm x = M.facePerm (M.alpha (M.alpha x))
    rw [M.alpha_involutive]
  exact Relation.EqvGen.trans _ (M.dual.alpha x) _
    (Relation.EqvGen.rel _ _ (Or.inr ⟨hx, rfl⟩)) (Relation.EqvGen.rel _ _ (Or.inl hface))

/-- A face class of the dual passes from the reverse of a dart to its rotation. -/
theorem eqvGen_sigma_of_alpha {M : CombMap.{v}} {keep : M.dual.Dart → Prop} (x : M.dual.Dart) :
    Relation.EqvGen (CombMap.FaceClassStep M.dual keep) (M.dual.alpha x) (M.dual.sigma x) := by
  have hface : M.dual.sigma x = M.dual.facePerm (M.dual.alpha x) := by
    change M.dual.sigma x = M.dual.sigma (M.dual.alpha (M.dual.alpha x))
    rw [M.dual.alpha_involutive]
  exact Relation.EqvGen.rel _ _ (Or.inl hface)

/-- A property shared by adjacent darts is shared along chains of adjacent darts. -/
theorem iff_of_eqvGen_adjacent {M : CombMap.{v}} {Q : M.Dart → Prop}
    (hadj : ∀ x z, M.Adjacent x z → (Q x ↔ Q z)) {x z : M.Dart}
    (h : Relation.EqvGen M.Adjacent x z) : Q x ↔ Q z := by
  induction h with
  | rel x₁ x₂ hx => exact hadj x₁ x₂ hx
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A dart on a relator cell that is not an end of the selected regions is not retained. -/
theorem ExtPhiData.not_phiKeepO_of_faceOf_eq_cell (P : ExtPhiData family E)
    {i : Fin Delta.rCellCount} (hi : some i ∉ endCellsO E) {x : (collapsedMap family).Dart}
    (hx : Delta.toCombMap.faceOf x.1 = (cell Delta i).face) : ¬ PhiKeepO family E x := by
  rintro ⟨a, ha, s, o, h⟩
  cases o with
  | true =>
      have hend : endFace Delta (sideCellO a s) = endFace Delta (some i) :=
        (faceOf_crossO_true a h).symm.trans hx
      apply hi
      rw [← endFace_injective Delta hend]
      exact sideCellO_mem_endCellsO ha s
  | false =>
      apply P.cell_not_mem a (P.subset ha) i
      rw [← hx]
      exact faceOf_crossO_false a h

/-- **The darts of a relator cell that is not an end lie in one face class** of the dual of the
collapsed map: around the cell, no dart is retained. -/
theorem ExtPhiData.eqvGen_of_faceOf_eq_cell (P : ExtPhiData family E)
    {i : Fin Delta.rCellCount} (hi : some i ∉ endCellsO E) {x x' : (collapsedMap family).Dart}
    (hx : Delta.toCombMap.faceOf x.1 = (cell Delta i).face)
    (hx' : Delta.toCombMap.faceOf x'.1 = (cell Delta i).face) :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E))
      x x' := by
  obtain ⟨k, hk⟩ :=
    ((Delta.toCombMap.faceOf_eq_iff x.1 x'.1).mp (hx.trans hx'.symm)).exists_nat_pow_eq
  induction k generalizing x with
  | zero =>
      rw [pow_zero, Equiv.Perm.one_apply] at hk
      rw [Subtype.ext hk]
      exact Relation.EqvGen.refl _
  | succ k ih =>
      have hface : ∀ a ∈ family, Delta.toCombMap.faceOf x.1 ∉ a.1 := by
        intro a ha
        rw [hx]
        exact P.cell_not_mem a ha i
      have hy : ((collapsedMap family).facePerm x).1 = Delta.toCombMap.facePerm x.1 :=
        congrArg Subtype.val (collapsed_facePerm_of_face_not_mem hface)
      rw [pow_succ, Equiv.Perm.mul_apply, ← hy] at hk
      refine Relation.EqvGen.trans _ _ _
        (eqvGen_facePerm_of_not_keep (M := collapsedMap family)
          (P.not_phiKeepO_of_faceOf_eq_cell hi hx))
        (ih (x := (collapsedMap family).facePerm x) ?_ hk)
      rw [hy, Delta.toCombMap.faceOf_facePerm, hx]

/-- **Walking around a face of the collapsed map** through darts that are not retained stays in
one face class of its dual. -/
theorem eqvGen_of_sameCycle_collapsed {keep : (collapsedMap family).dual.Dart → Prop}
    (S : (collapsedMap family).Dart → Prop)
    (hS : ∀ x, S x → S ((collapsedMap family).facePerm x)) (hkeep : ∀ x, S x → ¬ keep x)
    {x y : (collapsedMap family).Dart} (hx : S x)
    (hxy : (collapsedMap family).facePerm.SameCycle x y) :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual keep) x y := by
  obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction k generalizing x with
  | zero =>
      rw [pow_zero, Equiv.Perm.one_apply]
      exact Relation.EqvGen.refl _
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact Relation.EqvGen.trans _ _ _
        (eqvGen_facePerm_of_not_keep (M := collapsedMap family) (hkeep x hx))
        (ih (x := (collapsedMap family).facePerm x) (hS x hx))

/-- **The face `f` of `Φ'_M` holds the relator cell `i`**: the body of `HoldsCellO`. -/
def HoldsCellAtO (family E : Finset (RegionCandidate D eps Delta)) (f : (phiMapO family E).Face)
    (i : Fin Delta.rCellCount) : Prop :=
  some i ∉ endCellsO E ∧ ∃ d : (phiMapO family E).Dart, (phiMapO family E).faceOf d = f ∧
    ∃ x : (collapsedMap family).dual.Dart,
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E))
        d.1 x ∧ Delta.toCombMap.faceOf x.1 = (cell Delta i).face

theorem holdsCellO_iff {f : (phiMapO family E).Face} :
    HoldsCellO family E f ↔ ∃ i, HoldsCellAtO family E f i :=
  Iff.rfl

/-- **Two faces of `Φ'_M` holding the same relator cell are equal**, by
`CombMap.IsRestriction.faceOf_eq_of_faceClass`. -/
theorem ExtPhiData.eq_of_holdsCellAtO (P : ExtPhiData family E)
    (hM : (collapsedMap family).dual.IsPlanar) (hN : (phiMapO family E).IsConnected)
    {f f' : (phiMapO family E).Face} {i : Fin Delta.rCellCount}
    (hf : HoldsCellAtO family E f i) (hf' : HoldsCellAtO family E f' i) : f = f' := by
  obtain ⟨hi, d, rfl, x, hdx, hx⟩ := hf
  obtain ⟨-, d', rfl, x', hdx', hx'⟩ := hf'
  exact (phiMapO_isRestriction family E).faceOf_eq_of_faceClass hM hN
    (eqvGen_faceClassStep_range (Relation.EqvGen.trans _ _ _ hdx
      (Relation.EqvGen.trans _ _ _ (P.eqvGen_of_faceOf_eq_cell hi hx hx')
        (Relation.EqvGen.symm _ _ hdx'))))

/-- **Every dart of the dual of the collapsed map lies in the face class of a retained dart**: the
dual is connected, and a face class passes along both kinds of adjacency. -/
theorem ExtPhiData.exists_eqvGen_phiMapO (P : ExtPhiData family E)
    {a₀ : RegionCandidate D eps Delta} (ha₀ : a₀ ∈ E) (y : (collapsedMap family).dual.Dart) :
    ∃ d : (phiMapO family E).Dart,
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E))
        d.1 y := by
  have hstep : ∀ x z : (collapsedMap family).dual.Dart,
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E)) x z →
        ((∃ d : (phiMapO family E).Dart, Relation.EqvGen
            (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E)) d.1 x) ↔
          ∃ d : (phiMapO family E).Dart, Relation.EqvGen
            (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E)) d.1 z) :=
    fun _ _ h => ⟨fun ⟨d, hd⟩ => ⟨d, Relation.EqvGen.trans _ _ _ hd h⟩,
      fun ⟨d, hd⟩ => ⟨d, Relation.EqvGen.trans _ _ _ hd (Relation.EqvGen.symm _ _ h)⟩⟩
  have halpha : ∀ x : (collapsedMap family).dual.Dart,
      (∃ d : (phiMapO family E).Dart, Relation.EqvGen
          (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E)) d.1 x) ↔
        ∃ d : (phiMapO family E).Dart, Relation.EqvGen
          (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E)) d.1
            ((collapsedMap family).dual.alpha x) := by
    intro x
    by_cases hk : PhiKeepO family E x
    · exact ⟨fun _ => ⟨⟨_, (phiKeepO_alpha x).mpr hk⟩, Relation.EqvGen.refl _⟩,
        fun _ => ⟨⟨x, hk⟩, Relation.EqvGen.refl _⟩⟩
    · exact hstep _ _ (Relation.EqvGen.rel _ _ (Or.inr ⟨hk, rfl⟩))
  refine (iff_of_eqvGen_adjacent (Q := fun x => ∃ d : (phiMapO family E).Dart,
      Relation.EqvGen (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family E))
        d.1 x) ?_ (CombMap.dual_connected _ (collapsedMap_connected P.pairwise Delta.planar.1)
      (phiDartO P a₀ ha₀ true true).1 y)).mp ⟨phiDartO P a₀ ha₀ true true, Relation.EqvGen.refl _⟩
  rintro x z (rfl | rfl)
  · exact halpha x
  · exact (halpha x).trans (hstep _ _ (eqvGen_sigma_of_alpha x))

/-- A side cell of a region outside the linked component of `a₀` is not an end of that component. -/
theorem sideCellO_not_mem_endCellsO_of_not_mem {a₀ b : RegionCandidate D eps Delta} (hb : b ∈ E)
    (hbC : b ∉ linkedComponentO E a₀) (t : Bool) :
    sideCellO b t ∉ endCellsO (linkedComponentO E a₀) := by
  intro h
  obtain ⟨a, ha, s, hs⟩ := mem_endCellsO.mp h
  exact sideCellO_ne_of_not_mem_linkedComponentO ha hb hbC s t hs

/-- **A region outside the linked component of an exterior region joins two relator cells held by
one face of `Φ'_M`**: neither side cell is an end of the component, and the face class of the
crossing dart on its first side passes along its boundary to the crossing dart on its second side. -/
theorem ExtPhiData.exists_holdsCellAtO_of_not_mem (P : ExtPhiData family E)
    {a₀ b : RegionCandidate D eps Delta} (ha₀ : a₀ ∈ E) (ht₀ : a₀.2.target = none) (hb : b ∈ E)
    (hbC : b ∉ linkedComponentO E a₀) :
    ∃ j, b.2.target = some j ∧ ∃ f : (phiMapO family (linkedComponentO E a₀)).Face,
      HoldsCellAtO family (linkedComponentO E a₀) f b.2.source ∧
        HoldsCellAtO family (linkedComponentO E a₀) f j := by
  have hbF := P.subset hb
  obtain ⟨j, ht⟩ : ∃ j, b.2.target = some j := by
    cases h : b.2.target with
    | none =>
        exact (hbC (mem_linkedComponentO_of_sideCellO_eq_none (s := false) (t := false) ha₀ hb
          ht₀ h)).elim
    | some j => exact ⟨j, rfl⟩
  have hcross : ∀ w : (collapsedMap family).Dart, ∀ s o : Bool, crossO b s o = some w.1 →
      ¬ PhiKeepO family (linkedComponentO E a₀) w := by
    rintro w _ _ hw ⟨a, ha, _, _, h⟩
    exact hbC ((P.crossO_unique (linkedComponentO_subset E a₀ ha) hb h hw).1 ▸ ha)
  have hcycle : ∀ w : (collapsedMap family).Dart, w.1 ∈ b.2.boundary.cycle →
      ¬ PhiKeepO family (linkedComponentO E a₀) w := by
    rintro w hw ⟨a, ha, _, o, h⟩
    have hwb := ((b.2.boundary.cycle_mem_iff w.1).mp hw).1
    cases o with
    | true => exact P.face_not_mem_of_crossO_true h b hbF hwb
    | false =>
        exact hbC (eq_of_face_mem_of_face_mem P.pairwise
          (P.subset (linkedComponentO_subset E a₀ ha)) hbF (faceOf_crossO_false a h) hwb ▸ ha)
  obtain ⟨dT, hT⟩ := exists_crossO b (P.nondegenerate b hb) true true
  obtain ⟨dF, hF⟩ := exists_crossO b (P.nondegenerate b hb) false true
  have hcT := mem_cycle_crossO_false b ((crossO_alpha b true true dT).mpr hT)
  have hcF := mem_cycle_crossO_false b ((crossO_alpha b false true dF).mpr hF)
  have hkT := not_regionInternal_of_face_not_mem (P.face_not_mem_of_crossO_true hT)
  have hkF := not_regionInternal_of_face_not_mem (P.face_not_mem_of_crossO_true hF)
  have hchain : Relation.EqvGen
      (CombMap.FaceClassStep (collapsedMap family).dual (PhiKeepO family (linkedComponentO E a₀)))
      (⟨dT, hkT⟩ : (collapsedMap family).Dart) ⟨dF, hkF⟩ := by
    refine Relation.EqvGen.trans _
      (⟨_, not_regionInternal_of_mem_cycle P.pairwise hbF hcT⟩ : (collapsedMap family).Dart) _
      (Relation.EqvGen.rel _ _ (Or.inr ⟨hcross ⟨dT, hkT⟩ true true hT, rfl⟩)) ?_
    refine Relation.EqvGen.trans _
      (⟨_, not_regionInternal_of_mem_cycle P.pairwise hbF hcF⟩ : (collapsedMap family).Dart) _ ?_
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ (Or.inr ⟨hcross ⟨dF, hkF⟩ false true hF, rfl⟩)))
    exact eqvGen_of_sameCycle_collapsed (fun w => w.1 ∈ b.2.boundary.cycle)
      (fun w hw => mem_cycle_of_collapsed_faceOf_eq P.pairwise hbF hw _
        ((collapsedMap family).faceOf_facePerm w)) hcycle hcT
      (((collapsedMap family).faceOf_eq_iff _ _).mp
        (collapsed_faceOf_eq_of_mem_cycle P.pairwise hbF hcT hcF))
  obtain ⟨d, hd⟩ := (P.mono (linkedComponentO_subset E a₀)).exists_eqvGen_phiMapO
    (self_mem_linkedComponentO ha₀) ⟨dT, hkT⟩
  refine ⟨j, ht, (phiMapO family (linkedComponentO E a₀)).faceOf d,
    ⟨sideCellO_not_mem_endCellsO_of_not_mem hb hbC true, d, rfl, ⟨dT, hkT⟩, hd,
      faceOf_crossO_true b hT⟩,
    ⟨?_, d, rfl, ⟨dF, hkF⟩, Relation.EqvGen.trans _ _ _ hd hchain,
      (faceOf_crossO_true b hF).trans (congrArg (endFace Delta) ht)⟩⟩
  have h := sideCellO_not_mem_endCellsO_of_not_mem hb hbC false
  rwa [show sideCellO b false = some j from ht] at h

/-- The relator cells held by a face of `Φ'_M`. -/
noncomputable def heldCellsO (family E : Finset (RegionCandidate D eps Delta))
    (f : (phiMapO family E).Face) : Finset (Fin Delta.rCellCount) := by
  classical exact Finset.univ.filter fun i => HoldsCellAtO family E f i

theorem mem_heldCellsO {f : (phiMapO family E).Face} {i : Fin Delta.rCellCount} :
    i ∈ heldCellsO family E f ↔ HoldsCellAtO family E f i := by
  classical
  simp only [heldCellsO, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The regions of `E` outside `C` whose source cell is held by the face `f` of `Φ'_M` for `C`. -/
noncomputable def sourceRegionsO (E C : Finset (RegionCandidate D eps Delta))
    (f : (phiMapO family C).Face) : Finset (RegionCandidate D eps Delta) := by
  classical exact (E \ C).filter fun b => HoldsCellAtO family C f b.2.source

theorem mem_sourceRegionsO {C : Finset (RegionCandidate D eps Delta)}
    {f : (phiMapO family C).Face} {b : RegionCandidate D eps Delta} :
    b ∈ sourceRegionsO E C f ↔ (b ∈ E ∧ b ∉ C) ∧ HoldsCellAtO family C f b.2.source := by
  classical
  simp only [sourceRegionsO, Finset.mem_filter, Finset.mem_sdiff]

/-- **The count C5.** Every region of `E` outside the linked component `C` of an exterior region
has its source cell held by a face of `Φ'_M` for `C`. The regions with source cell held by one
face join cells held by that face, without multiple edges, so there are at most three per held
cell less three; a relator cell is held by at most one face. -/
theorem ExtPhiData.card_add_three_mul_le (P : ExtPhiData family E)
    (hmulti : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      a.JoinsCells i j → b.JoinsCells i j → False)
    {a₀ : RegionCandidate D eps Delta} (ha₀ : a₀ ∈ E) (ht₀ : a₀.2.target = none)
    (faces : Finset (phiMapO family (linkedComponentO E a₀)).Face)
    (hfaces : ∀ f, f ∈ faces ↔ HoldsCellO family (linkedComponentO E a₀) f)
    (cells : Finset (Fin Delta.rCellCount))
    (hcells : ∀ i, some i ∉ endCellsO (linkedComponentO E a₀) → i ∈ cells) :
    E.card + 3 * faces.card ≤ (linkedComponentO E a₀).card + 3 * cells.card := by
  classical
  have PC := P.mono (linkedComponentO_subset E a₀)
  have ha₀C := self_mem_linkedComponentO ha₀
  have hM := CombMap.dual_planar _
    (collapsedMap_planar P.pairwise (phiDartO PC a₀ ha₀C true true).1)
  have hN := phiMapO_connected PC (linked_linkedComponentO E a₀)
  have hsub : E \ linkedComponentO E a₀ ⊆
      faces.biUnion fun f => sourceRegionsO E (linkedComponentO E a₀) f := by
    intro b hb
    obtain ⟨hbE, hbC⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨_, _, f, hfs, _⟩ := P.exists_holdsCellAtO_of_not_mem ha₀ ht₀ hbE hbC
    exact Finset.mem_biUnion.mpr
      ⟨f, (hfaces f).mpr ⟨_, hfs⟩, mem_sourceRegionsO.mpr ⟨⟨hbE, hbC⟩, hfs⟩⟩
  have hEC : (E \ linkedComponentO E a₀).card ≤
      ∑ f ∈ faces, (sourceRegionsO E (linkedComponentO E a₀) f).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hface : ∀ f ∈ faces, (sourceRegionsO E (linkedComponentO E a₀) f).card + 3 ≤
      3 * (heldCellsO family (linkedComponentO E a₀) f).card := by
    intro f hf
    have hR : ∀ b ∈ sourceRegionsO E (linkedComponentO E a₀) f, b ∈ E ∧
        ∃ j, b.2.target = some j ∧ HoldsCellAtO family (linkedComponentO E a₀) f j := by
      intro b hb
      obtain ⟨⟨hbE, hbC⟩, hfs⟩ := mem_sourceRegionsO.mp hb
      obtain ⟨j, ht, f', hf's, hf'j⟩ := P.exists_holdsCellAtO_of_not_mem ha₀ ht₀ hbE hbC
      exact ⟨hbE, j, ht, PC.eq_of_holdsCellAtO hM hN hf's hfs ▸ hf'j⟩
    have PR : PhiData family (sourceRegionsO E (linkedComponentO E a₀) f) :=
      { subset := fun b hb => P.subset (hR b hb).1
        pairwise := P.pairwise
        cell_not_mem := P.cell_not_mem
        interior := fun b hb => by
          obtain ⟨_, j, ht, _⟩ := hR b hb
          simp only [ht, Option.isSome_some]
        nondegenerate := fun b hb => P.nondegenerate b (hR b hb).1
        noLoop := fun b hb => P.noLoop b (hR b hb).1
        noMultiple := fun a ha b hb hab i j => hmulti a (hR a ha).1 b (hR b hb).1 hab i j }
    obtain ⟨i, hi⟩ := (hfaces f).mp hf
    have hV := card_le_of_endpoints PR (heldCellsO family (linkedComponentO E a₀) f)
      (fun b hb s => by
        cases s with
        | true =>
            show b.2.source ∈ _
            exact mem_heldCellsO.mpr (mem_sourceRegionsO.mp hb).2
        | false =>
            obtain ⟨_, j, ht, hj⟩ := hR b hb
            show b.2.target.getD b.2.source ∈ _
            rw [ht]
            exact mem_heldCellsO.mpr hj)
      ⟨i, mem_heldCellsO.mpr hi⟩
    have hpos : 0 < (heldCellsO family (linkedComponentO E a₀) f).card :=
      Finset.card_pos.mpr ⟨i, mem_heldCellsO.mpr hi⟩
    omega
  have hdisj : (faces : Set (phiMapO family (linkedComponentO E a₀)).Face).PairwiseDisjoint
      fun f => heldCellsO family (linkedComponentO E a₀) f := by
    intro f _ f' _ hne
    exact Finset.disjoint_left.mpr fun i hi hi' =>
      hne (PC.eq_of_holdsCellAtO hM hN (mem_heldCellsO.mp hi) (mem_heldCellsO.mp hi'))
  have hcellsum :
      ∑ f ∈ faces, (heldCellsO family (linkedComponentO E a₀) f).card ≤ cells.card := by
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card fun i hi => ?_
    obtain ⟨f, -, hi⟩ := Finset.mem_biUnion.mp hi
    exact hcells i (mem_heldCellsO.mp hi).1
  have hsum : ∑ f ∈ faces, (sourceRegionsO E (linkedComponentO E a₀) f).card + faces.card * 3 ≤
      3 * ∑ f ∈ faces, (heldCellsO family (linkedComponentO E a₀) f).card := by
    have h := Finset.sum_le_sum hface
    rwa [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at h
  have hE : E.card ≤ (E \ linkedComponentO E a₀).card + (linkedComponentO E a₀).card :=
    Finset.card_le_card_sdiff_add_card
  omega

end Embedded.RegionCandidate

/-- **C5 of `PhiPrimeCountInput`**, unconditionally. -/
theorem cellFaceCountInput (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : CellFaceCountInput.{u, w, v} D eps W := by
  intro Delta family E P hmulti a₀ ha₀ ht₀
  exact P.card_add_three_mul_le hmulti ha₀ ht₀ _
    (fun f => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _
    (fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.eqvGen_faceClassStep_range
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.eqvGen_facePerm_of_not_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.eqvGen_sigma_of_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.iff_of_eqvGen_adjacent
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.not_phiKeepO_of_faceOf_eq_cell
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.eqvGen_of_faceOf_eq_cell
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.eqvGen_of_sameCycle_collapsed
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.eq_of_holdsCellAtO
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.exists_eqvGen_phiMapO
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.sideCellO_not_mem_endCellsO_of_not_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.exists_holdsCellAtO_of_not_mem
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_heldCellsO
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.mem_sourceRegionsO
#audit_axioms
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.ExtPhiData.card_add_three_mul_le
#audit_axioms GroupApproximation.GGT.VanKampen.cellFaceCountInput
