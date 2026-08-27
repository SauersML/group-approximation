import GroupApproximation.Matching.ComponentRefinement
import GroupApproximation.Matching.BlockTransport

/-!
# Refinement supplied by an expander decomposition

This specializes the finite component-refinement theorem to the edited graph
and block partition carried by `ExpanderDecomposition`.  Every source block now
has a canonically chosen dominant target block for a fixed compressor
permutation.
-/

namespace GroupApproximation
namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The edited graph, transported to the approximation model. -/
noncomputable abbrev modelGraph (n : ℕ) : FiniteMultiGraph :=
  (D.graph n).transport (S.model n) (D.vertexEquiv n)

/-- The edited graph induced on one component block. -/
noncomputable abbrev componentGraph (n : ℕ) (y : S.model n) : FiniteMultiGraph :=
  (D.modelGraph n).induce ((D.blocks n).block y)

/-- Its vertex type is definitionally the source block. -/
noncomputable abbrev componentVertexEquiv (n : ℕ) (y : S.model n) :
    (D.componentGraph n y).vertex ≃ (D.blocks n).block y :=
  Equiv.refl _

theorem componentGraph_expands (n : ℕ) (y : S.model n) :
    ((D.componentGraph n y).transport
      (blockModel (D.blocks n) y) (D.componentVertexEquiv n y)).HasCheegerLowerBound
        D.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound (D.componentGraph n y)
    (blockModel (D.blocks n) y) (D.componentVertexEquiv n y)
      (by simpa [componentGraph, modelGraph] using D.component_expands n y)

/-- Dominant target selected for a source component and a compressor
permutation. -/
noncomputable def refineAt (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (y : S.model n) :
    ComponentRefinement (D.componentGraph n y) (D.blocks n) Q q y :=
  refineComponent (D.componentGraph n y) (D.blocks n) Q q y
    (D.componentVertexEquiv n y) (D.componentGraph_expands n y)

/-- The one-component leakage bound furnished by the decomposition. -/
theorem refineAt_leakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (y : S.model n) :
    D.cheeger *
        ((((D.blocks n).block y).image q \ (D.refineAt Q q y).target).card : ℝ) ≤
      4 * (((D.componentGraph n y).transport (blockModel (D.blocks n) y)
        (D.componentVertexEquiv n y)).crossingEdges
          (componentTargetLabel (D.blocks n) Q q y)).card :=
  (D.refineAt Q q y).cheeger_mul_leakage_le_crossing

/-! ### Refinement indexed once per distinct source component -/

/-- The distinct source components at index `n`. -/
abbrev componentIndex (n : ℕ) := BlockIndex (D.blocks n)

/-- A representative vertex chosen only to access the vertex-indexed graph
interface.  The associated block is exactly the indexed component. -/
noncomputable def componentRepresentative (n : ℕ) (C : D.componentIndex n) :
    S.model n :=
  BlockIndex.representative (D.blocks n) C

@[simp] theorem componentRepresentative_block (n : ℕ)
    (C : D.componentIndex n) :
    (D.blocks n).block (D.componentRepresentative n C) = C.block :=
  BlockIndex.block_representative (D.blocks n) C

/-- Dominant target for one distinctly indexed source component. -/
noncomputable def refineBlock (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :=
  D.refineAt Q q (D.componentRepresentative n C)

/-- When source and target use the same component partition, bundle the
chosen dominant target as an index in that finite component type. -/
noncomputable def refineIndex (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) : D.componentIndex n := by
  let R := D.refineBlock (D.blocks n) q C
  refine ⟨R.target, ?_⟩
  obtain ⟨y, hy⟩ := R.target_isBlock
  exact ((D.blocks n).mem_blocksFinset R.target).mpr ⟨y, hy⟩

@[simp] theorem refineIndex_block (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) :
    (D.refineIndex q C).block =
      (D.refineBlock (D.blocks n) q C).target := rfl

/-- The leakage estimate, now indexed over each source component exactly once. -/
theorem refineBlock_leakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    D.cheeger * ((C.block.image q \ (D.refineBlock Q q C).target).card : ℝ) ≤
      4 * (((D.componentGraph n (D.componentRepresentative n C)).transport
        (blockModel (D.blocks n) (D.componentRepresentative n C))
          (D.componentVertexEquiv n (D.componentRepresentative n C))).crossingEdges
            (componentTargetLabel (D.blocks n) Q q
              (D.componentRepresentative n C))).card := by
  simpa [refineBlock] using D.refineAt_leakage Q q (D.componentRepresentative n C)

/-- Leakage mass of one distinctly indexed source component. -/
noncomputable def componentLeakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) : ℕ :=
  (C.block.image q \ (D.refineBlock Q q C).target).card

/-- For a self-refinement, overlap with the chosen target and one-sided
leakage partition the transported source block exactly. -/
theorem overlap_refineIndex_add_componentLeakage
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    BlockIndex.overlap (D.blocks n) q C (D.refineIndex q C) +
        D.componentLeakage (D.blocks n) q C = C.block.card := by
  classical
  have hsplit := Finset.card_sdiff_add_card_inter
    (C.block.image q) (D.refineIndex q C).block
  have himage : (C.block.image q).card = C.block.card :=
    Finset.card_image_of_injective C.block q.injective
  unfold BlockIndex.overlap componentLeakage
  rw [D.refineIndex_block] at hsplit ⊢
  omega

/-- Components on which at least half of the transported source is lost
before reaching the chosen target. -/
noncomputable def majorityLeakageBad (q : Equiv.Perm (S.model n)) :
    Finset (D.componentIndex n) :=
  Finset.univ.filter fun C ↦
    C.block.card ≤ 2 * D.componentLeakage (D.blocks n) q C

/-- Vertex mass carried by components without a strict majority in their
chosen overlap target. -/
noncomputable def majorityLeakageBadMass (q : Equiv.Perm (S.model n)) : ℝ :=
  (D.majorityLeakageBad q).sum fun C ↦ (C.block.card : ℝ)

/-- The non-majority component mass costs at most twice the total one-sided
leakage. -/
theorem majorityLeakageBadMass_le (q : Equiv.Perm (S.model n)) :
    D.majorityLeakageBadMass q ≤
      2 * ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) q C : ℝ) := by
  classical
  unfold majorityLeakageBadMass majorityLeakageBad
  calc
    ∑ C ∈ Finset.univ.filter (fun C : D.componentIndex n ↦
        C.block.card ≤ 2 * D.componentLeakage (D.blocks n) q C),
        (C.block.card : ℝ) ≤
      ∑ C ∈ Finset.univ.filter (fun C : D.componentIndex n ↦
        C.block.card ≤ 2 * D.componentLeakage (D.blocks n) q C),
        (2 * (D.componentLeakage (D.blocks n) q C : ℝ)) := by
          apply Finset.sum_le_sum
          intro C hC
          exact_mod_cast (Finset.mem_filter.mp hC).2
    _ ≤ ∑ C : D.componentIndex n,
        (2 * (D.componentLeakage (D.blocks n) q C : ℝ)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun _ _ _ ↦ by positivity)
    _ = 2 * ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) q C : ℝ) := by
          rw [Finset.mul_sum]

/-- Outside `majorityLeakageBad`, the chosen target contains a strict
majority of the transported source component. -/
theorem two_mul_overlap_gt_card_of_not_mem_majorityLeakageBad
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n)
    (hC : C ∉ D.majorityLeakageBad q) :
    C.block.card < 2 * BlockIndex.overlap (D.blocks n) q C (D.refineIndex q C) := by
  classical
  have hgood : 2 * D.componentLeakage (D.blocks n) q C < C.block.card := by
    simpa only [majorityLeakageBad, Finset.mem_filter, Finset.mem_univ, true_and,
      not_le] using hC
  have hsplit := D.overlap_refineIndex_add_componentLeakage q C
  omega

/-- On every good component, `refineIndex` is the unique target with strict
majority overlap. -/
theorem refineIndex_eq_of_two_mul_overlap_gt_card
    (q : Equiv.Perm (S.model n)) (C E : D.componentIndex n)
    (hC : C ∉ D.majorityLeakageBad q)
    (hE : C.block.card <
      2 * BlockIndex.overlap (D.blocks n) q C E) :
    D.refineIndex q C = E :=
  BlockIndex.eq_of_two_mul_overlap_gt_card (D.blocks n) q C
    (D.refineIndex q C) E
      (D.two_mul_overlap_gt_card_of_not_mem_majorityLeakageBad q C hC) hE

/-- Components on which the chosen target map fails to be reciprocal. -/
noncomputable def nonreciprocal (q : Equiv.Perm (S.model n)) :
    Finset (D.componentIndex n) :=
  Finset.univ.filter fun C ↦ D.refineIndex q (D.refineIndex q C) ≠ C

/-- Vertex mass carried by the nonreciprocal component locus. -/
noncomputable def nonreciprocalMass (q : Equiv.Perm (S.model n)) : ℝ :=
  (D.nonreciprocal q).sum fun C ↦ (C.block.card : ℝ)

/-- Components on which the chosen target maps for two permutations fail to
undo one another. -/
noncomputable def nonreciprocalPair (q r : Equiv.Perm (S.model n)) :
    Finset (D.componentIndex n) :=
  Finset.univ.filter fun C ↦ D.refineIndex r (D.refineIndex q C) ≠ C

/-- Vertex mass carried by failure of reciprocity for a permutation pair. -/
noncomputable def nonreciprocalPairMass (q r : Equiv.Perm (S.model n)) : ℝ :=
  (D.nonreciprocalPair q r).sum fun C ↦ (C.block.card : ℝ)

/-- If `r = q⁻¹`, failure of the two chosen component maps to undo one
another costs at most the sum of their two one-sided leakage totals. -/
theorem nonreciprocalPairMass_le_totalLeakage_add
    (q r : Equiv.Perm (S.model n)) (hr : r = q⁻¹) :
    D.nonreciprocalPairMass q r ≤
      (∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) q C : ℝ)) +
      ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) r C : ℝ) := by
  classical
  let R := D.nonreciprocalPair q r
  let f := D.refineIndex q
  let g := D.refineIndex r
  let eq : D.componentIndex n → ℝ := fun C ↦
    D.componentLeakage (D.blocks n) q C
  let er : D.componentIndex n → ℝ := fun C ↦
    D.componentLeakage (D.blocks n) r C
  let w : D.componentIndex n → D.componentIndex n → ℝ := fun C E ↦
    BlockIndex.overlap (D.blocks n) q C E
  have hsplit (C : D.componentIndex n) :
      (C.block.card : ℝ) = eq C + w C (f C) := by
    dsimp only [eq, w, f]
    rw [add_comm]
    exact_mod_cast (D.overlap_refineIndex_add_componentLeakage q C).symm
  have hreverse (C E : D.componentIndex n) :
      w C E = BlockIndex.overlap (D.blocks n) r E C := by
    dsimp only [w]
    rw [hr]
    exact_mod_cast BlockIndex.overlap_inv_comm (D.blocks n) q C E
  have hfiber (E : D.componentIndex n) :
      ∑ C ∈ R.filter (fun C ↦ f C = E), w C E ≤ er E := by
    let F := R.filter (fun C ↦ f C = E)
    have hsubset : F ⊆ (Finset.univ : Finset (D.componentIndex n)).erase (g E) := by
      intro C hC
      have hCR : C ∈ R := (Finset.mem_filter.mp hC).1
      have hfCE : f C = E := (Finset.mem_filter.mp hC).2
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ C⟩
      intro hCeq
      have hrecip : g (f C) = C := by rw [hfCE, ← hCeq]
      exact (Finset.mem_filter.mp hCR).2 hrecip
    have hsubsum :
        ∑ C ∈ F, (BlockIndex.overlap (D.blocks n) r E C : ℝ) ≤
          ∑ C ∈ (Finset.univ : Finset (D.componentIndex n)).erase (g E),
            (BlockIndex.overlap (D.blocks n) r E C : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ by positivity)
    have htotal := BlockIndex.sum_overlap (D.blocks n) r E
    have herase := Finset.sum_erase_add
      (Finset.univ : Finset (D.componentIndex n))
        (fun C ↦ (BlockIndex.overlap (D.blocks n) r E C : ℝ))
        (Finset.mem_univ (g E))
    have hchosen :
        (BlockIndex.overlap (D.blocks n) r E (g E) : ℝ) + er E =
          E.block.card := by
      dsimp only [g, er]
      exact_mod_cast D.overlap_refineIndex_add_componentLeakage r E
    have herase_eq :
        ∑ C ∈ (Finset.univ : Finset (D.componentIndex n)).erase (g E),
          (BlockIndex.overlap (D.blocks n) r E C : ℝ) = er E := by
      linarith
    calc
      ∑ C ∈ R.filter (fun C ↦ f C = E), w C E =
          ∑ C ∈ F, (BlockIndex.overlap (D.blocks n) r E C : ℝ) := by
            apply Finset.sum_congr rfl
            intro C _
            exact hreverse C E
      _ ≤ ∑ C ∈ (Finset.univ : Finset (D.componentIndex n)).erase (g E),
          (BlockIndex.overlap (D.blocks n) r E C : ℝ) := hsubsum
      _ = er E := herase_eq
  have hoverlap : ∑ C ∈ R, w C (f C) ≤ ∑ E, er E := by
    calc
      ∑ C ∈ R, w C (f C) =
          ∑ E, ∑ C ∈ R.filter (fun C ↦ f C = E), w C (f C) :=
            (Finset.sum_fiberwise R f (fun C ↦ w C (f C))).symm
      _ = ∑ E, ∑ C ∈ R.filter (fun C ↦ f C = E), w C E := by
            apply Finset.sum_congr rfl
            intro E _
            apply Finset.sum_congr rfl
            intro C hC
            rw [(Finset.mem_filter.mp hC).2]
      _ ≤ ∑ E, er E := Finset.sum_le_sum fun E _ ↦ hfiber E
  have hleakage : ∑ C ∈ R, eq C ≤ ∑ C, eq C :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun _ _ _ ↦ by positivity)
  calc
    D.nonreciprocalPairMass q r = ∑ C ∈ R, (C.block.card : ℝ) := rfl
    _ = ∑ C ∈ R, (eq C + w C (f C)) := by
      apply Finset.sum_congr rfl
      intro C _
      exact hsplit C
    _ = (∑ C ∈ R, eq C) + ∑ C ∈ R, w C (f C) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ C, eq C) + ∑ C, er C := add_le_add hleakage hoverlap
    _ = (∑ C : D.componentIndex n,
          (D.componentLeakage (D.blocks n) q C : ℝ)) +
        ∑ C : D.componentIndex n,
          (D.componentLeakage (D.blocks n) r C : ℝ) := by
      rfl

/-- For an involution, failure of reciprocity costs leakage.  More precisely,
the total mass of components with `f (f C) ≠ C`, where `f` is the chosen
target map, is at most twice the total one-sided leakage. -/
theorem nonreciprocalMass_le_two_mul_totalLeakage
    (q : Equiv.Perm (S.model n)) (hsq : q * q = 1) :
    D.nonreciprocalMass q ≤
      2 * ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) q C : ℝ) := by
  classical
  let R := D.nonreciprocal q
  let f := D.refineIndex q
  let e : D.componentIndex n → ℝ := fun C ↦
    D.componentLeakage (D.blocks n) q C
  let w : D.componentIndex n → D.componentIndex n → ℝ := fun C E ↦
    BlockIndex.overlap (D.blocks n) q C E
  have hsplit (C : D.componentIndex n) :
      (C.block.card : ℝ) = e C + w C (f C) := by
    dsimp only [e, w, f]
    rw [add_comm]
    exact_mod_cast (D.overlap_refineIndex_add_componentLeakage q C).symm
  have hsymm (C E : D.componentIndex n) : w C E = w E C := by
    dsimp only [w]
    exact_mod_cast BlockIndex.overlap_comm_of_sq (D.blocks n) q hsq C E
  have hfiber (E : D.componentIndex n) :
      ∑ C ∈ R.filter (fun C ↦ f C = E), w C E ≤ e E := by
    let F := R.filter (fun C ↦ f C = E)
    have hsubset : F ⊆ (Finset.univ : Finset (D.componentIndex n)).erase (f E) := by
      intro C hC
      have hCR : C ∈ R := (Finset.mem_filter.mp hC).1
      have hfCE : f C = E := (Finset.mem_filter.mp hC).2
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ C⟩
      intro hCeq
      have hrecip : f (f C) = C := by rw [hfCE, ← hCeq]
      exact (Finset.mem_filter.mp hCR).2 hrecip
    have hsubsum :
        ∑ C ∈ F, w E C ≤
          ∑ C ∈ (Finset.univ : Finset (D.componentIndex n)).erase (f E),
            w E C := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ by positivity)
    have htotal := BlockIndex.sum_overlap (D.blocks n) q E
    have herase := Finset.sum_erase_add
      (Finset.univ : Finset (D.componentIndex n)) (fun C ↦ w E C)
        (Finset.mem_univ (f E))
    have hchosen : w E (f E) + e E = E.block.card := by
      dsimp only [w, f, e]
      exact_mod_cast D.overlap_refineIndex_add_componentLeakage q E
    have herase_eq :
        ∑ C ∈ (Finset.univ : Finset (D.componentIndex n)).erase (f E),
          w E C = e E := by
      dsimp only [w] at htotal hchosen ⊢
      linarith
    calc
      ∑ C ∈ R.filter (fun C ↦ f C = E), w C E =
          ∑ C ∈ F, w E C := by
            apply Finset.sum_congr rfl
            intro C _
            exact hsymm C E
      _ ≤ ∑ C ∈ (Finset.univ : Finset (D.componentIndex n)).erase (f E),
          w E C := hsubsum
      _ = e E := herase_eq
  have hoverlap : ∑ C ∈ R, w C (f C) ≤ ∑ E, e E := by
    calc
      ∑ C ∈ R, w C (f C) =
          ∑ E, ∑ C ∈ R.filter (fun C ↦ f C = E), w C (f C) :=
            (Finset.sum_fiberwise R f (fun C ↦ w C (f C))).symm
      _ = ∑ E, ∑ C ∈ R.filter (fun C ↦ f C = E), w C E := by
            apply Finset.sum_congr rfl
            intro E _
            apply Finset.sum_congr rfl
            intro C hC
            rw [(Finset.mem_filter.mp hC).2]
      _ ≤ ∑ E, e E := Finset.sum_le_sum fun E _ ↦ hfiber E
  have hleakage : ∑ C ∈ R, e C ≤ ∑ C, e C :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun _ _ _ ↦ by positivity)
  calc
    D.nonreciprocalMass q = ∑ C ∈ R, (C.block.card : ℝ) := rfl
    _ = ∑ C ∈ R, (e C + w C (f C)) := by
      apply Finset.sum_congr rfl
      intro C _
      exact hsplit C
    _ = (∑ C ∈ R, e C) + ∑ C ∈ R, w C (f C) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ C, e C) + ∑ C, e C := add_le_add hleakage hoverlap
    _ = 2 * ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) q C : ℝ) := by
      dsimp only [e]
      ring

/-- The target-block label on the whole edited model graph. -/
def transportedTargetLabel (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (x : S.model n) : Finset (S.model n) :=
  Q.block (q x)

/-- Crossing occurrences in one component, viewed as occurrences of the whole
edited graph. -/
noncomputable def componentCrossingEdges (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    Finset (D.modelGraph n).edge :=
  Finset.univ.filter fun e ↦
    transportedTargetLabel Q q ((D.modelGraph n).first e) ≠
        transportedTargetLabel Q q ((D.modelGraph n).second e) ∧
      (D.modelGraph n).first e ∈ C.block ∧
      (D.modelGraph n).second e ∈ C.block

@[simp] theorem mem_componentCrossingEdges
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) (e : (D.modelGraph n).edge) :
    e ∈ D.componentCrossingEdges Q q C ↔
      e ∈ (D.modelGraph n).crossingEdges (transportedTargetLabel Q q) ∧
        (D.modelGraph n).first e ∈ C.block ∧
        (D.modelGraph n).second e ∈ C.block := by
  simp [componentCrossingEdges]

/-- The induced-component crossing count is exactly the count of the
corresponding ambient edge occurrences. -/
theorem component_crossing_card_eq
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) :
    (((D.componentGraph n (D.componentRepresentative n C)).transport
      (blockModel (D.blocks n) (D.componentRepresentative n C))
        (D.componentVertexEquiv n (D.componentRepresentative n C))).crossingEdges
          (componentTargetLabel (D.blocks n) Q q
            (D.componentRepresentative n C))).card =
      (D.componentCrossingEdges Q q C).card := by
  classical
  let y := D.componentRepresentative n C
  apply Finset.card_bij (fun a _ ↦ a.1)
  · intro a ha
    rw [D.mem_componentCrossingEdges]
    have hcross := (FiniteMultiGraph.mem_crossingEdges _ _ a).mp ha
    refine ⟨?_, ?_, ?_⟩
    · apply (FiniteMultiGraph.mem_crossingEdges _ _ a.1).mpr
      have hfirstEndpoint :
          ((D.componentVertexEquiv n (D.componentRepresentative n C))
            ((D.componentGraph n (D.componentRepresentative n C)).first a)).1 =
              (D.modelGraph n).first a.1 := rfl
      have hsecondEndpoint :
          ((D.componentVertexEquiv n (D.componentRepresentative n C))
            ((D.componentGraph n (D.componentRepresentative n C)).second a)).1 =
              (D.modelGraph n).second a.1 := rfl
      change Q.block (q ((D.modelGraph n).first a.1)) ≠
        Q.block (q ((D.modelGraph n).second a.1))
      change Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).first a)).1) ≠
        Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).second a)).1) at hcross
      rwa [hfirstEndpoint, hsecondEndpoint] at hcross
    · rw [← D.componentRepresentative_block n C]
      exact a.2.1
    · rw [← D.componentRepresentative_block n C]
      exact a.2.2
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro e he
    rw [D.mem_componentCrossingEdges] at he
    have hfirst : (D.modelGraph n).first e ∈ (D.blocks n).block y := by
      dsimp [y]
      rw [D.componentRepresentative_block n C]
      exact he.2.1
    have hsecond : (D.modelGraph n).second e ∈ (D.blocks n).block y := by
      dsimp [y]
      rw [D.componentRepresentative_block n C]
      exact he.2.2
    let a : (D.componentGraph n y).edge := ⟨e, hfirst, hsecond⟩
    refine ⟨a, ?_, rfl⟩
    apply (FiniteMultiGraph.mem_crossingEdges _ _ a).mpr
    have hcross := (FiniteMultiGraph.mem_crossingEdges _ _ e).mp he.1
    have hfirstEndpoint :
        ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).first a)).1 =
            (D.modelGraph n).first e := rfl
    have hsecondEndpoint :
        ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).second a)).1 =
            (D.modelGraph n).second e := rfl
    change Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
        ((D.componentGraph n (D.componentRepresentative n C)).first a)).1) ≠
      Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
        ((D.componentGraph n (D.componentRepresentative n C)).second a)).1)
    change Q.block (q ((D.modelGraph n).first e)) ≠
      Q.block (q ((D.modelGraph n).second e)) at hcross
    rwa [hfirstEndpoint, hsecondEndpoint]

theorem componentCrossingEdges_pairwise
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    (↑(Finset.univ : Finset (D.componentIndex n)) : Set (D.componentIndex n)).PairwiseDisjoint
      (D.componentCrossingEdges Q q) := by
  intro C _ E _ hCE
  apply Finset.disjoint_left.mpr
  intro e heC heE
  rw [D.mem_componentCrossingEdges] at heC heE
  have hblocks := BlockIndex.pairwise_disjoint (D.blocks n)
    (Finset.mem_univ C) (Finset.mem_univ E) hCE
  exact Finset.disjoint_left.mp hblocks heC.2.1 heE.2.1

/-- The component crossing sets partition all crossing occurrences because
every edited edge stays inside a unique source component. -/
theorem componentCrossingEdges_biUnion
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    (Finset.univ : Finset (D.componentIndex n)).biUnion
        (D.componentCrossingEdges Q q) =
      (D.modelGraph n).crossingEdges (transportedTargetLabel Q q) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
    exact (D.mem_componentCrossingEdges Q q C e).mp heC |>.1
  · intro he
    let C : D.componentIndex n :=
      ⟨(D.blocks n).block ((D.modelGraph n).first e),
        (D.blocks n).block_mem_blocksFinset ((D.modelGraph n).first e)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨C, Finset.mem_univ C, (D.mem_componentCrossingEdges Q q C e).mpr
      ⟨he, ?_, ?_⟩⟩
    · exact (D.blocks n).self_mem _
    · change (D.modelGraph n).second e ∈
        (D.blocks n).block ((D.modelGraph n).first e)
      rw [D.edge_inside n e]
      exact (D.blocks n).self_mem _

/-- Refined crossing count of one distinctly indexed source component. -/
noncomputable def componentCrossingCount (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) : ℕ :=
  (D.componentCrossingEdges Q q C).card

theorem sum_componentCrossingCount
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    ∑ C : D.componentIndex n, D.componentCrossingCount Q q C =
      ((D.modelGraph n).crossingEdges (transportedTargetLabel Q q)).card := by
  classical
  have hcard := Finset.card_biUnion (s :=
      (Finset.univ : Finset (D.componentIndex n)))
    (t := D.componentCrossingEdges Q q)
      fun C hC E hE hCE ↦ D.componentCrossingEdges_pairwise Q q hC hE hCE
  rw [D.componentCrossingEdges_biUnion Q q] at hcard
  simpa [componentCrossingCount] using hcard.symm

/-- Summing the componentwise refinement inequalities counts every source
component once. -/
theorem cheeger_mul_totalLeakage_le_crossings
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    D.cheeger * ∑ C : D.componentIndex n, (D.componentLeakage Q q C : ℝ) ≤
      4 * ∑ C : D.componentIndex n, (D.componentCrossingCount Q q C : ℝ) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun C _ ↦ by
    rw [componentLeakage, componentCrossingCount, ← D.component_crossing_card_eq Q q C]
    exact D.refineBlock_leakage Q q C

/-- The summed refinement estimate with its right-hand side reduced to the
single global crossing count. -/
theorem cheeger_mul_totalLeakage_le_globalCrossing
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    D.cheeger * ∑ C : D.componentIndex n, (D.componentLeakage Q q C : ℝ) ≤
      4 * (((D.modelGraph n).crossingEdges (transportedTargetLabel Q q)).card : ℝ) := by
  have h := D.cheeger_mul_totalLeakage_le_crossings Q q
  have hsum :
      (∑ C : D.componentIndex n, (D.componentCrossingCount Q q C : ℝ)) =
        (((D.modelGraph n).crossingEdges (transportedTargetLabel Q q)).card : ℝ) := by
    exact_mod_cast D.sum_componentCrossingCount Q q
  rwa [hsum] at h

/-- Any sequence of permutations with negligible crossings of the edited
component graph has negligible total refinement leakage.  This form applies
to external approximate centralizers as well as ambient compressors. -/
theorem totalLeakage_negligible_of_crossing
    (q : ∀ n, Equiv.Perm (S.model n))
    (hcross : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ (((D.modelGraph n).crossingEdges
        (transportedTargetLabel (D.blocks n) (q n))).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) C : ℝ) := by
  have hscaled := Negligible.const_mul (4 / D.cheeger) hcross
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hscaled
  have hrefine := D.cheeger_mul_totalLeakage_le_globalCrossing
    (D.blocks n) (q n)
  have hle : (∑ C : D.componentIndex n,
      (D.componentLeakage (D.blocks n) (q n) C : ℝ)) ≤
      (4 / D.cheeger) *
        (((D.modelGraph n).crossingEdges
          (transportedTargetLabel (D.blocks n) (q n))).card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ D.cheeger_pos).2
    rw [mul_comm]
    exact hrefine
  apply div_le_div_of_nonneg_right hle
  positivity

/-- Exact involutivity plus negligible total leakage makes failure of the
chosen component target map to square to the identity negligible in vertex
mass. -/
theorem nonreciprocalMass_negligible_of_totalLeakage
    (q : ∀ n, Equiv.Perm (S.model n))
    (hsq : ∀ n, q n * q n = 1)
    (hleak : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) C : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ D.nonreciprocalMass (q n) := by
  have htwice := Negligible.const_mul 2 hleak
  refine Vanishing.squeeze
    (fun n ↦ div_nonneg (by
      unfold nonreciprocalMass
      positivity) (by positivity))
    (fun n ↦ ?_) htwice
  apply div_le_div_of_nonneg_right
  · exact D.nonreciprocalMass_le_two_mul_totalLeakage (q n) (hsq n)
  · positivity

/-- Exact inverse model permutations and negligible leakage in both
directions make failure of the two chosen component maps to undo one another
negligible in vertex mass. -/
theorem nonreciprocalPairMass_negligible_of_totalLeakage
    (q r : ∀ n, Equiv.Perm (S.model n))
    (hinv : ∀ n, r n = (q n)⁻¹)
    (hleakq : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (q n) C : ℝ))
    (hleakr : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ C : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (r n) C : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ D.nonreciprocalPairMass (q n) (r n) := by
  have hsum := Negligible.add hleakq hleakr
  refine Vanishing.squeeze
    (fun n ↦ div_nonneg (by
      unfold nonreciprocalPairMass
      positivity) (by positivity))
    (fun n ↦ ?_) hsum
  apply div_le_div_of_nonneg_right
  · exact D.nonreciprocalPairMass_le_totalLeakage_add (q n) (r n) (hinv n)
  · positivity

end ExpanderDecomposition
end GroupApproximation
