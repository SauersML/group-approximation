import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin recognition, part 1: recognition of rigid polars is support separation

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Lane `sk-flip-19` (Rubin route).

`RigidPolarRecognitionStatement` (RubinPolarReduce.lean) says that every rigid polar `P` of `[[S]]`
is `F_O` for an open `O`.  This file shows it is equivalent to `RigidPolarSupportSeparationStatement`:
for every rigid polar `P`, each `p ∈ P` and each `q ∈ C(P)` have disjoint moved sets.

* `rigidPolarSupportSeparation_of_rigidPolarRecognition`: if `P = F_O` with `O` open, then
  `C(P) = F_{Oᶜ}` (`centralizer_rubinRigidSubgroup`).  So `movedSet p ⊆ O` and
  `movedSet q ⊆ Oᶜ`.
* `rigidPolarRecognition_of_rigidPolarSupportSeparation`: take `O = ⋃_{p ∈ P} movedSet p`.  It is
  open, since moved sets are open in a Hausdorff space.
  - `P ≤ F_O` holds by definition of `O`.
  - Each `q ∈ C(P)` is supported in `Oᶜ`, by separation, so `q ∈ F_{Oᶜ} = C(F_O)`.
  - Hence every `k ∈ F_O` commutes with all of `C(P)`, and `k ∈ C(C(P)) = P`.

The equivalence locates the failure of recognition: it fails exactly when some rigid polar
overlaps its centraliser.  RubinRecognitionFalse.lean shows on paper that this happens (LOUD:
recognition is FALSE in general).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- Support separation for rigid polars: every element of a rigid polar `P` of `[[S]]` and every
element of its centraliser have disjoint moved sets.  Equivalent to
`RigidPolarRecognitionStatement`, and FALSE in general (RubinRecognitionFalse.lean). -/
def RigidPolarSupportSeparationStatement : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    [PerfectSpace Y] [Nonempty Y] [TopologicalSpace.MetrizableSpace Y] (S : Y ≃ₜ Y),
    IsMinimalHomeo S → ∀ P : Subgroup (topologicalFullGroup S), IsRigidPolar P →
      ∀ p ∈ P, ∀ q ∈ Subgroup.centralizer (P : Set (topologicalFullGroup S)),
        Disjoint (movedSet ((p : topologicalFullGroup S) : Y ≃ₜ Y))
          (movedSet ((q : topologicalFullGroup S) : Y ≃ₜ Y))

/-- Recognition of rigid polars implies support separation. -/
theorem rigidPolarSupportSeparation_of_rigidPolarRecognition
    (h : RigidPolarRecognitionStatement) : RigidPolarSupportSeparationStatement :=
  fun Y _ _ _ _ _ _ _ S hS P hP p hp q hq => by
    obtain ⟨O, hO, rfl⟩ := h Y S hS P hP
    have hp' : SupportedIn ((p : topologicalFullGroup S) : Y ≃ₜ Y) O :=
      mem_rubinRigidSubgroup.1 hp
    have hq' : q ∈ rubinRigidSubgroup S Oᶜ := by
      rw [← centralizer_rubinRigidSubgroup hS hO]
      exact hq
    have hq'' : SupportedIn ((q : topologicalFullGroup S) : Y ≃ₜ Y) Oᶜ :=
      mem_rubinRigidSubgroup.1 hq'
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    exact (supportedIn_iff_movedSet_subset.1 hq'' hy2)
      (supportedIn_iff_movedSet_subset.1 hp' hy1)

/-- Support separation implies recognition of rigid polars, with
`O = ⋃_{p ∈ P} movedSet p`. -/
theorem rigidPolarRecognition_of_rigidPolarSupportSeparation
    (h : RigidPolarSupportSeparationStatement) : RigidPolarRecognitionStatement :=
  fun Y _ _ _ _ _ _ _ S hS P hP => by
    obtain ⟨hcc, -, -, -⟩ := hP
    have hO : IsOpen (⋃ p : P, movedSet (((p : topologicalFullGroup S) : Y ≃ₜ Y))) :=
      isOpen_iUnion fun p => isOpen_movedSet_of_t2Space _
    refine ⟨⋃ p : P, movedSet (((p : topologicalFullGroup S) : Y ≃ₜ Y)), hO,
      le_antisymm (fun p hp => ?_) (fun k hk => ?_)⟩
    · exact mem_rubinRigidSubgroup.2 (supportedIn_iff_movedSet_subset.2 fun y hy =>
        Set.mem_iUnion.2 ⟨⟨p, hp⟩, hy⟩)
    · rw [hcc, Subgroup.mem_centralizer_iff]
      intro q hq
      have hqsupp : SupportedIn ((q : topologicalFullGroup S) : Y ≃ₜ Y)
          (⋃ p : P, movedSet (((p : topologicalFullGroup S) : Y ≃ₜ Y)))ᶜ := by
        refine supportedIn_iff_movedSet_subset.2 fun y hy => Set.mem_compl fun hyO => ?_
        obtain ⟨p, hpy⟩ := Set.mem_iUnion.1 hyO
        exact Set.disjoint_left.1 (h Y S hS P ⟨hcc, ‹_›, ‹_›, ‹_›⟩ p p.2 q hq) hpy hy
      sorry
