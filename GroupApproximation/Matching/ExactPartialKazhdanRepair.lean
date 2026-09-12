import GroupApproximation.Kazhdan.DiagonalInvariantRelation
import GroupApproximation.Matching.PartialBijectionRelation
import GroupApproximation.Matching.PartialSwapEquivariance
import GroupApproximation.Matching.PartialEquivarianceComposition
import GroupApproximation.Matching.PartialClusterCandidates

/-!
# Exact Kazhdan repair for finite partial intertwiners

A partial bijection between two finite `G`-sets is encoded by its swap
involution on their disjoint union.  The two actions combine to an exact
action on that union.  Applying diagonal Kazhdan repair to the swap and then
extracting its left-to-right crossings produces a repaired partial
bijection.  This file gives the explicit two-sided distance estimate needed
by the finite cluster-composition interface.
-/

namespace GroupApproximation
namespace ExactPartialKazhdanRepair

open DiagonalInvariantRelation
open FinitePartialBijection
open KazhdanImprovement
open scoped symmDiff

universe u

variable {G : Type u} [Group G]
variable {Y Z : FiniteModel}

/-- Componentwise exact action on a disjoint union. -/
def sumActionHom (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z) :
    G →* Equiv.Perm (sumModel Y Z) where
  toFun g := sumAction σY σZ g
  map_one' := by
    ext x
    cases x <;> simp [sumAction]
  map_mul' g h := by
    ext x
    cases x <;> simp [sumAction]

@[simp] theorem sumActionHom_apply
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (g : G) (x : Y ⊕ Z) :
    sumActionHom σY σZ g x = Sum.map (σY g) (σZ g) x := by
  cases x <;> rfl

/-- The left-to-right part of a relation on a disjoint union. -/
def crossingRelation (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) :
    Finset (Y × Z) :=
  Finset.univ.filter fun p ↦ (Sum.inl p.1, Sum.inr p.2) ∈ U

@[simp] theorem mem_crossingRelation
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) (y : Y) (z : Z) :
    (y, z) ∈ crossingRelation U ↔ (Sum.inl y, Sum.inr z) ∈ U := by
  simp [crossingRelation]

/-- Singleton rows of a relation remain right-unique after restricting to
left-to-right crossings. -/
theorem crossingRelation_relationCore_right_unique
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) :
    ∀ {y z w}, (y, z) ∈ crossingRelation (relationCore (sumModel Y Z) U) →
      (y, w) ∈ crossingRelation (relationCore (sumModel Y Z) U) → z = w := by
  intro y z w hyz hyw
  rw [mem_crossingRelation] at hyz hyw
  have h := relationCore_right_unique (sumModel Y Z) U hyz hyw
  exact Sum.inr.inj h

/-- Singleton columns of a relation remain left-unique after restricting to
left-to-right crossings. -/
theorem crossingRelation_relationCore_left_unique
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) :
    ∀ {y x z}, (y, z) ∈ crossingRelation (relationCore (sumModel Y Z) U) →
      (x, z) ∈ crossingRelation (relationCore (sumModel Y Z) U) → y = x := by
  intro y x z hyz hxz
  rw [mem_crossingRelation] at hyz hxz
  have h := relationCore_left_unique (sumModel Y Z) U hyz hxz
  exact Sum.inl.inj h

/-- The partial bijection carried by the singleton-fiber left-to-right core
of a relation.  Unlike `repairRelation`, this performs no arbitrary
completion, so exact invariance of the core can be retained. -/
noncomputable def coreCrossing
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) : FinitePartialBijection Y Z :=
  ofBiuniqueRelation
    (crossingRelation (relationCore (sumModel Y Z) U))
    (crossingRelation_relationCore_right_unique U)
    (crossingRelation_relationCore_left_unique U)

/-- The graph of `coreCrossing` is literally the crossing part of the
singleton-fiber core. -/
theorem graph_coreCrossing
    (U : Finset ((Y ⊕ Z) × (Y ⊕ Z))) :
    (coreCrossing U).graph =
      crossingRelation (relationCore (sumModel Y Z) U) := by
  exact graph_ofBiuniqueRelation _ _ _

/-- Exact relation-core repair of a partial arrow.  This differs from
`repair`: it never completes the invariant singleton-fiber core to an
arbitrary permutation. -/
noncomputable def exactCoreRepair
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) : FinitePartialBijection Y Z :=
  coreCrossing (roundedDiagonalRelation (sumActionHom σY σZ)
    (permutationGraph (sumModel Y Z) b.swapPerm))

/-- The graph of the exact core repair is invariant under every group
element. -/
theorem exactCoreRepair_graph_mapsTo
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) (g : G) (y : Y) (z : Z)
    (hyz : (y, z) ∈ (exactCoreRepair σY σZ b).graph) :
    (σY g y, σZ g z) ∈ (exactCoreRepair σY σZ b).graph := by
  rw [exactCoreRepair, graph_coreCrossing, mem_crossingRelation] at hyz ⊢
  have hmapped := relationCore_roundedDiagonalRelation_mapsTo
    (sumActionHom σY σZ)
    (permutationGraph (sumModel Y Z) b.swapPerm) g hyz
  have heq : diagonalActionHom (sumActionHom σY σZ) g
      (Sum.inl y, Sum.inr z) =
        (Sum.inl (σY g y), Sum.inr (σZ g z)) := rfl
  rw [heq] at hmapped
  exact hmapped

/-- In a transitive source action, any nonempty exact core repair has full
source. -/
theorem exactCoreRepair_source_eq_univ_of_transitive
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (htransY : ∀ x y : Y, ∃ g : G, σY g x = y)
    (hne : (exactCoreRepair σY σZ b).source.Nonempty) :
    (exactCoreRepair σY σZ b).source = Finset.univ := by
  exact source_eq_univ_of_graph_mapsTo_of_transitive σY σZ
    (exactCoreRepair σY σZ b)
    (exactCoreRepair_graph_mapsTo σY σZ b) htransY hne

/-- In a transitive target action, any nonempty exact core repair has full
target. -/
theorem exactCoreRepair_target_eq_univ_of_transitive
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (htransZ : ∀ x y : Z, ∃ g : G, σZ g x = y)
    (hne : (exactCoreRepair σY σZ b).target.Nonempty) :
    (exactCoreRepair σY σZ b).target = Finset.univ := by
  exact target_eq_univ_of_graph_mapsTo_of_transitive σY σZ
    (exactCoreRepair σY σZ b)
    (exactCoreRepair_graph_mapsTo σY σZ b) htransZ hne

/-- Nonempty exact core repair between two transitive actions is a full
equivariant bijection. -/
theorem exactCoreRepair_source_target_eq_univ_of_transitive
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (htransY : ∀ x y : Y, ∃ g : G, σY g x = y)
    (htransZ : ∀ x y : Z, ∃ g : G, σZ g x = y)
    (hne : (exactCoreRepair σY σZ b).source.Nonempty) :
    (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ := by
  have hsource := exactCoreRepair_source_eq_univ_of_transitive
    σY σZ b htransY hne
  obtain ⟨y, hy⟩ := hne
  have htargetNonempty : (exactCoreRepair σY σZ b).target.Nonempty :=
    ⟨(exactCoreRepair σY σZ b).apply y hy,
      (exactCoreRepair σY σZ b).apply_mem_target y hy⟩
  exact ⟨hsource, exactCoreRepair_target_eq_univ_of_transitive
    σY σZ b htransZ htargetNonempty⟩

/-- If fewer than one third of the original source graph edges can be lost
to relation edits and bad fibers, then the exact core repair has a nonempty
crossing. -/
theorem exactCoreRepair_source_nonempty_of_three_mul_edits_lt
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hedits :
      3 * (((permutationGraph (sumModel Y Z) b.swapPerm \
          roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm)).card) +
        ((roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm) \
          permutationGraph (sumModel Y Z) b.swapPerm).card)) <
        b.source.card) :
    (exactCoreRepair σY σZ b).source.Nonempty := by
  let P := permutationGraph (sumModel Y Z) b.swapPerm
  let R := roundedDiagonalRelation (sumActionHom σY σZ) P
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  let F : ↥b.source →
      ↥(missingSources (sumModel Y Z)
        (relationCore (sumModel Y Z) R) b.swapPerm) := fun y ↦ by
    refine ⟨Sum.inl y.1, ?_⟩
    rw [mem_missingSources]
    intro hcore
    have hcross : (y.1, b.apply y.1 y.2) ∈
        crossingRelation (relationCore (sumModel Y Z) R) := by
      rw [mem_crossingRelation]
      simpa only [swapPerm_inl_of_mem b y.1 y.2] using hcore
    have hgraph : (y.1, b.apply y.1 y.2) ∈
        (exactCoreRepair σY σZ b).graph := by
      rw [exactCoreRepair, graph_coreCrossing]
      exact hcross
    obtain ⟨hsource, _⟩ :=
      (mem_graph (exactCoreRepair σY σZ b) y.1
        (b.apply y.1 y.2)).mp hgraph
    rw [hempty] at hsource
    exact (Finset.notMem_empty _ hsource).elim
  have hF : Function.Injective F := by
    intro y x h
    apply Subtype.ext
    exact Sum.inl.inj (congrArg Subtype.val h)
  have hsourceLe : b.source.card ≤
      (missingSources (sumModel Y Z)
        (relationCore (sumModel Y Z) R) b.swapPerm).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective F hF
  have hcoreBound :=
    card_missingSources_relationCore_le_three_edits
      (sumModel Y Z) R b.swapPerm
  dsimp only [P, R] at hsourceLe
  dsimp only [P, R] at hcoreBound
  omega

/-- A strict Kazhdan defect budget makes the invariant core repair a full
equivariant bijection between transitive finite actions. -/
theorem exactCoreRepair_source_target_eq_univ_of_kazhdan
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (htransY : ∀ x y : Y, ∃ g : G, σY g x = y)
    (htransZ : ∀ x y : Z, ∃ g : G, σZ g x = y)
    (b : FinitePartialBijection Y Z)
    (hsmall :
      24 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
          ε ^ 2 * (b.source.card : ℝ)) :
    (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ := by
  let P := permutationGraph (sumModel Y Z) b.swapPerm
  let R := roundedDiagonalRelation (sumActionHom σY σZ) P
  let E : ℕ := (P \ R).card + (R \ P).card
  have hround := kazhdan_mul_card_graph_symmDiff_rounded_le_defect
    hQ (sumActionHom σY σZ) b.swapPerm
  have hE : E = (P ∆ R).card := by
    simpa [E, Nat.add_comm] using
      card_sdiff_add_card_sdiff_eq_symmDiff P R
  have hroundE : ε ^ 2 * (E : ℝ) ≤
      8 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
    dsimp only [P, R] at hround
    rw [hE]
    exact hround
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have heditsReal : (3 * E : ℝ) < b.source.card := by
    have hscaled : ε ^ 2 * (3 * E : ℝ) ≤
        24 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
      nlinarith
    nlinarith
  have heditsNat : 3 * E < b.source.card := by
    exact_mod_cast heditsReal
  have hnonempty := exactCoreRepair_source_nonempty_of_three_mul_edits_lt
    σY σZ b (by simpa only [P, R, E] using heditsNat)
  exact exactCoreRepair_source_target_eq_univ_of_transitive
    σY σZ b htransY htransZ hnonempty

/-- Once the exact core repair is full, its labeled forward defect is
literally empty. -/
theorem exactCoreRepair_equivarianceDefect_eq_empty
    {Q : Finset G}
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hsource : (exactCoreRepair σY σZ b).source = Finset.univ) :
    (exactCoreRepair σY σZ b).equivarianceDefect
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) = ∅ := by
  exact equivarianceDefect_eq_empty_of_graph_mapsTo_of_source_eq_univ
    (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)
    (exactCoreRepair σY σZ b)
    (fun q ↦ exactCoreRepair_graph_mapsTo σY σZ b q.1) hsource

/-- Fullness also makes the labeled equivariance defect of the inverse
literally empty. -/
theorem exactCoreRepair_symm_equivarianceDefect_eq_empty
    {Q : Finset G}
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (htarget : (exactCoreRepair σY σZ b).target = Finset.univ) :
    (exactCoreRepair σY σZ b).symm.equivarianceDefect
      (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1) = ∅ := by
  exact equivarianceDefect_eq_empty_of_graph_mapsTo_of_source_eq_univ
    (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)
    (exactCoreRepair σY σZ b).symm
    (fun q ↦ symm_graph_mapsTo_of_graph_mapsTo σY σZ
      (exactCoreRepair σY σZ b)
      (exactCoreRepair_graph_mapsTo σY σZ b) q.1)
    (by simpa only [symm_source] using htarget)

/-- A full exact core repair is a cluster candidate at every positive
expansion threshold and every positive scale: all three candidate defects
vanish exactly. -/
theorem exactCoreRepair_isClusterCandidate_of_source_target_eq_univ
    {Q : Finset G}
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hfull : (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ)
    {h : ℝ} {m : ℕ} (hh : 0 < h) (hm : 0 < m) :
    (exactCoreRepair σY σZ b).IsClusterCandidate
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [FinitePartialBijection.sourceDefect,
      FinitePartialBijection.targetDefect, hfull.1, hfull.2,
      Finset.card_univ, Nat.sub_self, zero_add]
    omega
  · rw [exactCoreRepair_equivarianceDefect_eq_empty σY σZ b hfull.1]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · rw [exactCoreRepair_symm_equivarianceDefect_eq_empty σY σZ b hfull.2]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- If the exact repair is full on the source, every forward disagreement
with the original partial arrow supplies a discarded edge of the original
swap-permutation graph. -/
theorem card_disagreement_exactCoreRepair_le_core_edits
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hsource : (exactCoreRepair σY σZ b).source = Finset.univ) :
    (b.disagreement (exactCoreRepair σY σZ b)).card ≤
      (permutationGraph (sumModel Y Z) b.swapPerm \
        relationCore (sumModel Y Z)
          (roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm))).card := by
  classical
  let r := exactCoreRepair σY σZ b
  let C := relationCore (sumModel Y Z)
    (roundedDiagonalRelation (sumActionHom σY σZ)
      (permutationGraph (sumModel Y Z) b.swapPerm))
  let charge : {y // y ∈ b.disagreement r} →
      {p // p ∈ permutationGraph (sumModel Y Z) b.swapPerm \ C} := fun y ↦ by
    refine ⟨(Sum.inl y.1, b.swapPerm (Sum.inl y.1)), ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨(mem_permutationGraph (sumModel Y Z) b.swapPerm _).2 rfl, ?_⟩
    intro hcore
    have hry : y.1 ∈ r.source := by
      rw [hsource]
      exact Finset.mem_univ _
    have hrgraph : (y.1, r.apply y.1 hry) ∈ r.graph :=
      (mem_graph r y.1 (r.apply y.1 hry)).2 ⟨hry, rfl⟩
    have hrepairCore :
        (Sum.inl y.1, Sum.inr (r.apply y.1 hry)) ∈ C := by
      change (y.1, r.apply y.1 hry) ∈
        (coreCrossing (roundedDiagonalRelation (sumActionHom σY σZ)
          (permutationGraph (sumModel Y Z) b.swapPerm))).graph at hrgraph
      rw [graph_coreCrossing, mem_crossingRelation] at hrgraph
      exact hrgraph
    have hunique := relationCore_right_unique (sumModel Y Z)
      _ hcore hrepairCore
    by_cases hyb : y.1 ∈ b.source
    · have heq : b.apply y.1 hyb = r.apply y.1 hry := by
        apply Sum.inr.inj
        simpa only [swapPerm_inl_of_mem b y.1 hyb] using hunique
      exact (mem_disagreement b r y.1).1 y.2 hyb hry heq
    · exact Sum.inl_ne_inr (by
        simpa only [swapPerm_inl_of_not_mem b y.1 hyb] using hunique)
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Sum.inl.inj (congrArg (fun p ↦ p.1.1) hxy)
  simpa only [Fintype.card_coe, C, r] using
    Fintype.card_le_of_injective charge hcharge

/-- The inverse disagreement obeys the same discarded-core-edge bound,
using columns of the singleton-fiber core. -/
theorem card_symm_disagreement_exactCoreRepair_le_core_edits
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (htarget : (exactCoreRepair σY σZ b).target = Finset.univ) :
    (b.symm.disagreement (exactCoreRepair σY σZ b).symm).card ≤
      (permutationGraph (sumModel Y Z) b.swapPerm \
        relationCore (sumModel Y Z)
          (roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm))).card := by
  classical
  let r := exactCoreRepair σY σZ b
  let C := relationCore (sumModel Y Z)
    (roundedDiagonalRelation (sumActionHom σY σZ)
      (permutationGraph (sumModel Y Z) b.swapPerm))
  let charge : {z // z ∈ b.symm.disagreement r.symm} →
      {p // p ∈ permutationGraph (sumModel Y Z) b.swapPerm \ C} := fun z ↦ by
    refine ⟨(b.swapPerm (Sum.inr z.1), Sum.inr z.1), ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [mem_permutationGraph]
      have hsquare := DFunLike.congr_fun (swapPerm_mul_self b) (Sum.inr z.1)
      simpa using hsquare.symm
    · intro hcore
      have hrz : z.1 ∈ r.target := by
        rw [htarget]
        exact Finset.mem_univ _
      let y := r.symm.apply z.1 hrz
      have hry : y ∈ r.source := r.symm.apply_mem_target z.1 hrz
      have hrgraph : (y, z.1) ∈ r.graph := by
        rw [mem_graph]
        exact ⟨hry, r.apply_symm_apply z.1 hrz⟩
      have hrepairCore : (Sum.inl y, Sum.inr z.1) ∈ C := by
        change (y, z.1) ∈
          (coreCrossing (roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm))).graph at hrgraph
        rw [graph_coreCrossing, mem_crossingRelation] at hrgraph
        exact hrgraph
      have hunique := relationCore_left_unique (sumModel Y Z)
        _ hrepairCore hcore
      by_cases hzb : z.1 ∈ b.target
      · have heq : b.symm.apply z.1 hzb = r.symm.apply z.1 hrz := by
          apply Sum.inl.inj
          simpa only [y, swapPerm_inr_of_mem b z.1 hzb] using hunique.symm
        exact (mem_disagreement b.symm r.symm z.1).1 z.2 hzb hrz heq
      · exact Sum.inl_ne_inr (by
          simpa only [swapPerm_inr_of_not_mem b z.1 hzb] using hunique)
  have hcharge : Function.Injective charge := by
    intro x y hxy
    apply Subtype.ext
    exact Sum.inr.inj (congrArg (fun p ↦ p.1.2) hxy)
  simpa only [Fintype.card_coe, C, r] using
    Fintype.card_le_of_injective charge hcharge

/-- A full exact core repair differs from the original partial arrow on at
most twice the number of original swap-graph edges discarded by the core. -/
theorem twoSidedDisagreement_exactCoreRepair_le_two_mul_core_edits
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hfull : (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ) :
    b.twoSidedDisagreement (exactCoreRepair σY σZ b) ≤
      2 * (permutationGraph (sumModel Y Z) b.swapPerm \
        relationCore (sumModel Y Z)
          (roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm))).card := by
  rw [FinitePartialBijection.twoSidedDisagreement]
  have hf := card_disagreement_exactCoreRepair_le_core_edits
    σY σZ b hfull.1
  have hb := card_symm_disagreement_exactCoreRepair_le_core_edits
    σY σZ b hfull.2
  omega

/-- Passing to the singleton-fiber core costs at most six times the total
directed relation-edit budget in two-sided partial disagreement. -/
theorem twoSidedDisagreement_exactCoreRepair_le_six_mul_edits
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hfull : (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ) :
    b.twoSidedDisagreement (exactCoreRepair σY σZ b) ≤
      6 * (((permutationGraph (sumModel Y Z) b.swapPerm \
          roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm)).card) +
        ((roundedDiagonalRelation (sumActionHom σY σZ)
            (permutationGraph (sumModel Y Z) b.swapPerm) \
          permutationGraph (sumModel Y Z) b.swapPerm).card)) := by
  let R := roundedDiagonalRelation (sumActionHom σY σZ)
    (permutationGraph (sumModel Y Z) b.swapPerm)
  have htwo := twoSidedDisagreement_exactCoreRepair_le_two_mul_core_edits
    σY σZ b hfull
  have hcore := card_missingSources_relationCore_le_three_edits
    (sumModel Y Z) R b.swapPerm
  rw [card_missingSources] at hcore
  dsimp only [R] at hcore
  omega

/-- Quantitative closeness of a full exact core repair, with all constants
visible: Kazhdan rounding converts the factor-six core loss into `48` times
the original total commutation defect. -/
theorem kazhdan_mul_twoSidedDisagreement_exactCoreRepair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hfull : (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ) :
    ε ^ 2 * (b.twoSidedDisagreement (exactCoreRepair σY σZ b) : ℝ) ≤
      48 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let P := permutationGraph (sumModel Y Z) b.swapPerm
  let R := roundedDiagonalRelation (sumActionHom σY σZ) P
  let E : ℕ := (P \ R).card + (R \ P).card
  have htwoNat := twoSidedDisagreement_exactCoreRepair_le_six_mul_edits
    σY σZ b hfull
  have htwo : (b.twoSidedDisagreement (exactCoreRepair σY σZ b) : ℝ) ≤
      6 * (E : ℝ) := by
    dsimp only [P, R, E]
    exact_mod_cast htwoNat
  have hround := kazhdan_mul_card_graph_symmDiff_rounded_le_defect
    hQ (sumActionHom σY σZ) b.swapPerm
  have hE : E = (P ∆ R).card := by
    simpa [E, Nat.add_comm] using
      card_sdiff_add_card_sdiff_eq_symmDiff P R
  have hroundE : ε ^ 2 * (E : ℝ) ≤
      8 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
    dsimp only [P, R] at hround
    rw [hE]
    exact hround
  have hεsq : 0 ≤ ε ^ 2 := sq_nonneg ε
  nlinarith

/-- Under the explicit strict defect bound, the exact core repair is close
to the original partial arrow at the prescribed integer scale. -/
theorem twoSidedDisagreement_exactCoreRepair_lt_two_mul_of_kazhdan
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z)
    (hfull : (exactCoreRepair σY σZ b).source = Finset.univ ∧
      (exactCoreRepair σY σZ b).target = Finset.univ)
    {m : ℕ}
    (hclose : 48 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
      ε ^ 2 * (2 * m : ℕ)) :
    (exactCoreRepair σY σZ b).twoSidedDisagreement b < 2 * m := by
  have hbound := kazhdan_mul_twoSidedDisagreement_exactCoreRepair_le
    hQ σY σZ b hfull
  rw [twoSidedDisagreement_comm]
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hreal : (b.twoSidedDisagreement (exactCoreRepair σY σZ b) : ℝ) <
      (2 * m : ℕ) := by
    nlinarith
  exact_mod_cast hreal

/-- Complete exact-repair package for transitive finite actions: one
explicit smallness bound makes the core full and hence a zero-defect cluster
candidate, while a second explicit bound keeps it within the cluster radius. -/
theorem exactCoreRepair_candidate_and_close_of_kazhdan
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (htransY : ∀ x y : Y, ∃ g : G, σY g x = y)
    (htransZ : ∀ x y : Z, ∃ g : G, σZ g x = y)
    (b : FinitePartialBijection Y Z)
    {h : ℝ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hfullBound : 24 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
      ε ^ 2 * (b.source.card : ℝ))
    (hcloseBound : 48 * (totalCommutationDefect
        (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
      ε ^ 2 * (2 * m : ℕ)) :
    (exactCoreRepair σY σZ b).IsClusterCandidate
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m ∧
      (exactCoreRepair σY σZ b).twoSidedDisagreement b < 2 * m := by
  have hfull := exactCoreRepair_source_target_eq_univ_of_kazhdan
    hQ hε σY σZ htransY htransZ b hfullBound
  exact ⟨exactCoreRepair_isClusterCandidate_of_source_target_eq_univ
      σY σZ b hfull hh hm,
    twoSidedDisagreement_exactCoreRepair_lt_two_mul_of_kazhdan
      hQ hε σY σZ b hfull hcloseBound⟩

/-- Repair the swap permutation and extract its crossing partial map. -/
noncomputable def repair
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) : FinitePartialBijection Y Z :=
  extractCrossing
    (roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm)

/-- Repair introduces at most one new missing source for each point where the
rounded permutation differs from the original swap. -/
theorem sourceDefect_repair_le
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    (repair σY σZ b).sourceDefect ≤ b.sourceDefect +
      (hammingDisagreement b.swapPerm
        (roundedDiagonalPermutation
          (sumActionHom σY σZ) b.swapPerm)).card := by
  exact sourceDefect_extractCrossing_le b
    (roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm)

/-- The same edit budget controls new missing targets. -/
theorem targetDefect_repair_le
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    (repair σY σZ b).targetDefect ≤ b.targetDefect +
      (hammingDisagreement b.swapPerm
        (roundedDiagonalPermutation
          (sumActionHom σY σZ) b.swapPerm)).card := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have h := targetDefect_extractCrossing_le b p
  rw [card_hammingDisagreement_inv b.swapPerm p] at h
  exact h

/-- Both missing-endpoint budgets after repair are controlled by the original
missing mass and twice the rounded-permutation edit count. -/
theorem missingMass_repair_le
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    (repair σY σZ b).sourceDefect + (repair σY σZ b).targetDefect ≤
      b.sourceDefect + b.targetDefect +
        2 * (hammingDisagreement b.swapPerm
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)).card := by
  have hs := sourceDefect_repair_le σY σZ b
  have ht := targetDefect_repair_le σY σZ b
  omega

/-- The original forward and backward partial-equivariance defects, summed
with generator labels retained.  `Unit` packages one label at a time so no
collision between equal finite permutations can erase multiplicity. -/
noncomputable def partialTotalDefect
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) : ℕ :=
  ∑ q ∈ Q,
    ((b.equivarianceDefect
        (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)).card +
      (b.symm.equivarianceDefect
        (fun _ : Unit ↦ σZ q) (fun _ : Unit ↦ σY q)).card)

/-- The tagged defect over the subtype `Q` is exactly the sum of the
one-label defects.  This prevents either overcounting or loss of multiplicity
when passing between the candidate and Kazhdan-repair interfaces. -/
theorem card_taggedEquivarianceDefect_eq_sum_singleton
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) :
    (b.equivarianceDefect
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card =
      ∑ q : ↥Q,
        (b.equivarianceDefect
          (fun _ : Unit ↦ σY q.1) (fun _ : Unit ↦ σZ q.1)).card := by
  classical
  let F :
      {d // d ∈ b.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)} →
        Σ q : ↥Q, {d // d ∈ b.equivarianceDefect
          (fun _ : Unit ↦ σY q.1) (fun _ : Unit ↦ σZ q.1)} := fun d ↦ by
    refine ⟨d.1.1, ⟨(Unit.unit, d.1.2), ?_⟩⟩
    have hd := (mem_equivarianceDefect b
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) d.1).mp d.2
    rw [mem_equivarianceDefect]
    exact hd
  have hF : Function.Bijective F := by
    constructor
    · intro d e hde
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x ↦ x.1) hde
      · exact congrArg (fun x ↦ x.2.1.2) hde
    · rintro ⟨q, ⟨⟨u, y⟩, hy⟩⟩
      cases u
      have htag : (q, y) ∈ b.equivarianceDefect
          (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) := by
        rw [mem_equivarianceDefect] at hy ⊢
        exact hy
      refine ⟨⟨(q, y), htag⟩, ?_⟩
      rfl
  let e := Equiv.ofBijective F hF
  have hcard := Fintype.card_congr e
  rw [Fintype.card_sigma] at hcard
  simpa only [Fintype.card_coe] using hcard

/-- `partialTotalDefect` is precisely the sum of the forward and backward
candidate defect cardinalities with `Q` retained as a subtype. -/
theorem partialTotalDefect_eq_tagged
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) :
    partialTotalDefect σY σZ Q b =
      (b.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card +
      (b.symm.equivarianceDefect
        (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)).card := by
  rw [card_taggedEquivarianceDefect_eq_sum_singleton,
    card_taggedEquivarianceDefect_eq_sum_singleton]
  unfold partialTotalDefect
  rw [Finset.sum_add_distrib]
  rw [← Q.sum_attach, ← Q.sum_attach]
  rw [Finset.attach_eq_univ]

/-- Native total defect is subadditive under composition of partial
intertwiners, with all four forward/backward input contributions explicit. -/
theorem partialTotalDefect_trans_le
    {X : FiniteModel}
    (σX : G →* Equiv.Perm X) (σY : G →* Equiv.Perm Y)
    (σZ : G →* Equiv.Perm Z) (Q : Finset G)
    (f : FinitePartialBijection X Y)
    (g : FinitePartialBijection Y Z) :
    partialTotalDefect σX σZ Q (f.trans g) ≤
      (f.equivarianceDefect
        (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1)).card +
      (g.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card +
      (f.symm.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σX q.1)).card +
      (g.symm.equivarianceDefect
        (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)).card := by
  classical
  rw [partialTotalDefect_eq_tagged]
  have hforward := card_equivarianceDefect_trans_le
    (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1)
    (fun q : ↥Q ↦ σZ q.1) f g
  have hbackward := card_equivarianceDefect_trans_le
    (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)
    (fun q : ↥Q ↦ σX q.1) g.symm f.symm
  rw [f.symm_trans g]
  omega

/-- Candidate bounds turn the preceding four-term estimate into the clean
strict real budget `2 h m`. -/
theorem partialTotalDefect_trans_lt_two_mul
    {X : FiniteModel}
    (σX : G →* Equiv.Perm X) (σY : G →* Equiv.Perm Y)
    (σZ : G →* Equiv.Perm Z) (Q : Finset G)
    (f : FinitePartialBijection X Y)
    (hf : f.IsClusterCandidate
      (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1) h m)
    (g : FinitePartialBijection Y Z)
    (hg : g.IsClusterCandidate
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m) :
    (partialTotalDefect σX σZ Q (f.trans g) : ℝ) < 2 * h * m := by
  have htotalNat := partialTotalDefect_trans_le σX σY σZ Q f g
  have htotal : (partialTotalDefect σX σZ Q (f.trans g) : ℝ) ≤
      ((f.equivarianceDefect
        (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1)).card +
      (g.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card +
      (f.symm.equivarianceDefect
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σX q.1)).card +
      (g.symm.equivarianceDefect
        (fun q : ↥Q ↦ σZ q.1) (fun q : ↥Q ↦ σY q.1)).card : ℕ) := by
    exact_mod_cast htotalNat
  push_cast at htotal
  nlinarith [hf.forwardSmall, hf.backwardSmall,
    hg.forwardSmall, hg.backwardSmall]

/-- For one label, every bad arc of the swap embeds into the tagged
commutation-defect set used by the partial-equivariance comparison. -/
theorem card_badArcs_singleton_swap_le_sumCommutationDefect
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (q : G) (b : FinitePartialBijection Y Z) :
    (AlmostAutomorphism.badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm).card ≤
      (sumCommutationDefect b.swapPerm
        (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)).card := by
  let F :
      {p // p ∈ AlmostAutomorphism.badArcs (sumModel Y Z)
        {sumAction σY σZ q} b.swapPerm} →
      {p // p ∈ sumCommutationDefect b.swapPerm
        (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)} := fun p ↦ by
    refine ⟨(Unit.unit, p.1.2), ?_⟩
    rw [mem_sumCommutationDefect]
    have hp := (AlmostAutomorphism.mem_badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm p.1).1 p.2
    have hlabel : p.1.1 = sumAction σY σZ q := by simpa using hp.1
    rw [hlabel] at hp
    change b.swapPerm (sumAction σY σZ q p.1.2) ≠
      sumAction σY σZ q (b.swapPerm p.1.2)
    exact hp.2
  have hF : Function.Injective F := by
    intro p r hpr
    apply Subtype.ext
    have hvertex : p.1.2 = r.1.2 :=
      congrArg (fun x ↦ x.1.2) hpr
    have hp := (AlmostAutomorphism.mem_badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm p.1).1 p.2
    have hr := (AlmostAutomorphism.mem_badArcs (sumModel Y Z)
      {sumAction σY σZ q} b.swapPerm r.1).1 r.2
    have hpLabel : p.1.1 = sumAction σY σZ q := by simpa using hp.1
    have hrLabel : r.1.1 = sumAction σY σZ q := by simpa using hr.1
    exact Prod.ext (hpLabel.trans hrLabel.symm) hvertex
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF

/-- The swap commutation defect is bounded by the sum of the original
forward and backward partial-equivariance defects. -/
theorem totalCommutationDefect_swap_le_partialTotalDefect
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (b : FinitePartialBijection Y Z) :
    totalCommutationDefect (sumActionHom σY σZ) Q b.swapPerm ≤
      partialTotalDefect σY σZ Q b := by
  rw [totalCommutationDefect, partialTotalDefect]
  apply Finset.sum_le_sum
  intro q _
  refine (card_badArcs_singleton_swap_le_sumCommutationDefect
    σY σZ q b).trans ?_
  exact card_swapEquivarianceDefect_le b
    (fun _ : Unit ↦ σY q) (fun _ : Unit ↦ σZ q)

/-- Exact Kazhdan improvement for a composite of two cluster candidates.
The single scale-free numerical condition `48 h < ε²` makes the invariant
core both full and closer than the cluster radius. -/
theorem exactCoreRepair_trans_candidate_and_close
    {X : FiniteModel}
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (σX : G →* Equiv.Perm X) (σY : G →* Equiv.Perm Y)
    (σZ : G →* Equiv.Perm Z)
    (htransX : ∀ x y : X, ∃ g : G, σX g x = y)
    (htransZ : ∀ x y : Z, ∃ g : G, σZ g x = y)
    {h : ℝ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hnumeric : 48 * h < ε ^ 2)
    (hsizeX : 17 * m ≤ Fintype.card X)
    (f : FinitePartialBijection X Y)
    (hf : f.IsClusterCandidate
      (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σY q.1) h m)
    (g : FinitePartialBijection Y Z)
    (hg : g.IsClusterCandidate
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m) :
    (exactCoreRepair σX σZ (f.trans g)).IsClusterCandidate
        (fun q : ↥Q ↦ σX q.1) (fun q : ↥Q ↦ σZ q.1) h m ∧
      (exactCoreRepair σX σZ (f.trans g)).twoSidedDisagreement
        (f.trans g) < 2 * m := by
  let b := f.trans g
  let D := totalCommutationDefect (sumActionHom σX σZ) Q b.swapPerm
  have hpartial := partialTotalDefect_trans_lt_two_mul
    σX σY σZ Q f hf g hg
  have hDnat := totalCommutationDefect_swap_le_partialTotalDefect
    σX σZ Q b
  have hDle : (D : ℝ) ≤ (partialTotalDefect σX σZ Q b : ℝ) := by
    exact_mod_cast hDnat
  have hDlt : (D : ℝ) < 2 * h * m := hDle.trans_lt (by
    simpa only [b] using hpartial)
  have hfSelf := hf.selfSmall
  have hgSelf := hg.selfSmall
  have hfSource : f.sourceDefect < 2 * m := by omega
  have hgSource : g.sourceDefect < 2 * m := by omega
  have hbDefectLe : b.sourceDefect ≤ f.sourceDefect + g.sourceDefect := by
    exact sourceDefect_trans_le f g
  have hbDefect : b.sourceDefect < 4 * m := by omega
  have hbSourceLe : b.source.card ≤ Fintype.card X := Finset.card_le_univ _
  have hbSplit : b.sourceDefect + b.source.card = Fintype.card X := by
    unfold FinitePartialBijection.sourceDefect
    omega
  have hmSource : m ≤ b.source.card := by omega
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmSourceReal : (m : ℝ) ≤ b.source.card := by exact_mod_cast hmSource
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hfullBound :
      24 * (totalCommutationDefect
          (sumActionHom σX σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * (b.source.card : ℝ) := by
    dsimp only [D] at hDlt
    nlinarith
  have hcloseBound :
      48 * (totalCommutationDefect
          (sumActionHom σX σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * (2 * m : ℕ) := by
    dsimp only [D] at hDlt
    push_cast
    nlinarith
  exact exactCoreRepair_candidate_and_close_of_kazhdan
    hQ hε σX σZ htransX htransZ b hh hm hfullBound hcloseBound

/-- Retaining every element of `Q` as a distinct label costs at most a
factor `|Q|` relative to the bad-arc set indexed by the finite image of the
action.  The explicit first coordinate makes the charge injective even when
two group elements induce the same finite permutation. -/
theorem card_taggedSumCommutationDefect_le_card_mul_badArcs
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (Q : Finset G) (p : Equiv.Perm (sumModel Y Z)) :
    (sumCommutationDefect p
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card ≤
      Q.card *
        (AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ)) p).card := by
  classical
  let charge :
      {d // d ∈ sumCommutationDefect p
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)} →
        ↥Q × {a // a ∈ AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ)) p} := fun d ↦ by
    refine ⟨d.1.1, ⟨(sumAction σY σZ d.1.1.1, d.1.2), ?_⟩⟩
    rw [AlmostAutomorphism.mem_badArcs]
    refine ⟨Finset.mem_image.mpr ⟨d.1.1.1, d.1.1.2, ?_⟩, ?_⟩
    · rfl
    · exact (mem_sumCommutationDefect p
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) d.1).mp d.2
  have hcharge : Function.Injective charge := by
    intro d e hde
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x ↦ x.1) hde
    · exact congrArg (fun x ↦ x.2.1.2) hde
  have hcard := Fintype.card_le_of_injective charge hcharge
  simpa only [Fintype.card_coe, Fintype.card_prod] using hcard

/-- The repaired arrow is close to the original partial arrow.  The intrinsic
missing source and target masses are retained explicitly; every additional
disagreement is controlled by the Kazhdan repair of the swap permutation. -/
theorem kazhdan_mul_twoSidedDisagreement_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * (b.twoSidedDisagreement (repair σY σZ b) : ℝ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htwoNat :=
    twoSidedDisagreement_extractCrossing_le_self_add_two_mul b p
  have htwo : (b.twoSidedDisagreement (extractCrossing p) : ℝ) ≤
      (b.sourceDefect + b.targetDefect : ℕ) +
        2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    exact_mod_cast htwoNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left htwo (sq_nonneg ε)
  change ε ^ 2 * (b.twoSidedDisagreement (extractCrossing p) : ℝ) ≤ _
  nlinarith

/-- Quantitative preservation of co-large source and target sets under the
same exact Kazhdan repair. -/
theorem kazhdan_mul_missingMass_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have hmissingNat := missingMass_repair_le σY σZ b
  have hmissing :
      ((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) ≤
        (b.sourceDefect + b.targetDefect : ℕ) +
          2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    simpa only [p] using hmissingNat
  have hmissingReal :
      (((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) : ℝ) ≤
        (b.sourceDefect + b.targetDefect : ℕ) +
          2 * ((hammingDisagreement b.swapPerm p).card : ℕ) := by
    exact_mod_cast hmissing
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left hmissingReal (sq_nonneg ε)
  nlinarith

/-- Source-side form of the missing-mass estimate. -/
theorem kazhdan_mul_sourceDefect_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * ((repair σY σZ b).sourceDefect : ℝ) ≤
      ε ^ 2 * (b.sourceDefect : ℝ) +
        8 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have hsNat := sourceDefect_repair_le σY σZ b
  have hs : ((repair σY σZ b).sourceDefect : ℝ) ≤
      (b.sourceDefect : ℝ) +
        ((hammingDisagreement b.swapPerm p).card : ℝ) := by
    exact_mod_cast hsNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left hs (sq_nonneg ε)
  nlinarith

/-- Target-side form of the missing-mass estimate. -/
theorem kazhdan_mul_targetDefect_repair_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * ((repair σY σZ b).targetDefect : ℝ) ≤
      ε ^ 2 * (b.targetDefect : ℝ) +
        8 * (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htNat := targetDefect_repair_le σY σZ b
  have ht : ((repair σY σZ b).targetDefect : ℝ) ≤
      (b.targetDefect : ℝ) +
        ((hammingDisagreement b.swapPerm p).card : ℝ) := by
    exact_mod_cast htNat
  have hsymm :
      hammingDisagreement b.swapPerm p =
        hammingDisagreement p b.swapPerm := by
    ext x
    simp [hammingDisagreement, ne_comm]
  have hham :=
    kazhdan_mul_card_hammingDisagreement_roundedDiagonalPermutation_le
      hQ (sumActionHom σY σZ) b.swapPerm
  rw [← hsymm] at hham
  have hscaled := mul_le_mul_of_nonneg_left ht (sq_nonneg ε)
  nlinarith

/-- The same distance estimate expressed entirely in the native forward and
backward partial-equivariance defects of the input arrow. -/
theorem kazhdan_mul_twoSidedDisagreement_repair_le_partialDefect
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 * (b.twoSidedDisagreement (repair σY σZ b) : ℝ) ≤
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
        16 * (partialTotalDefect σY σZ Q b : ℝ) := by
  have hrepair := kazhdan_mul_twoSidedDisagreement_repair_le hQ σY σZ b
  have hdefectNat :=
    totalCommutationDefect_swap_le_partialTotalDefect σY σZ Q b
  have hdefect :
      (totalCommutationDefect (sumActionHom σY σZ) Q b.swapPerm : ℝ) ≤
        partialTotalDefect σY σZ Q b := by
    exact_mod_cast hdefectNat
  linarith

/-- The repaired swap itself has quantitatively controlled commutation
defect for the finite image of `Q`. -/
theorem kazhdan_mul_card_badArcs_repairedSwap_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((AlmostAutomorphism.badArcs (sumModel Y Z)
          (Q.image (sumActionHom σY σZ))
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)).card : ℝ) ≤
      8 * (Q.card : ℝ) *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) :=
  kazhdan_mul_card_badArcs_roundedDiagonalPermutation_le
    hQ (sumActionHom σY σZ) b.swapPerm

/-- Forward `Q`-tagged commutation defects of the repaired swap, with no
loss of labels that happen to act by the same finite permutation. -/
theorem kazhdan_mul_card_taggedSumCommutationDefect_repaired_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((sumCommutationDefect
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)
          (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
      8 * (Q.card : ℝ) ^ 2 *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htagNat :=
    card_taggedSumCommutationDefect_le_card_mul_badArcs σY σZ Q p
  have htag :
      ((sumCommutationDefect p
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
        (Q.card : ℝ) *
          (AlmostAutomorphism.badArcs (sumModel Y Z)
            (Q.image (sumActionHom σY σZ)) p).card := by
    exact_mod_cast htagNat
  have hbad := kazhdan_mul_card_badArcs_repairedSwap_le hQ σY σZ b
  have hscaled := mul_le_mul_of_nonneg_left htag (sq_nonneg ε)
  have hQ0 : 0 ≤ (Q.card : ℝ) := by positivity
  nlinarith

/-- The inverse repaired permutation has the same bad-arc cardinality, so
the identical quantitative bound controls backward tagged defects. -/
theorem kazhdan_mul_card_taggedSumCommutationDefect_repaired_inv_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) :
    ε ^ 2 *
        ((sumCommutationDefect
          (roundedDiagonalPermutation
            (sumActionHom σY σZ) b.swapPerm)⁻¹
          (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
      8 * (Q.card : ℝ) ^ 2 *
        (totalCommutationDefect
          (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have htagNat :=
    card_taggedSumCommutationDefect_le_card_mul_badArcs σY σZ Q p⁻¹
  have htag :
      ((sumCommutationDefect p⁻¹
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)).card : ℝ) ≤
        (Q.card : ℝ) *
          (AlmostAutomorphism.badArcs (sumModel Y Z)
            (Q.image (sumActionHom σY σZ)) p⁻¹).card := by
    exact_mod_cast htagNat
  have hbad := kazhdan_mul_card_badArcs_repairedSwap_le hQ σY σZ b
  rw [AlmostAutomorphism.card_badArcs_inv] at htag
  have hscaled := mul_le_mul_of_nonneg_left htag (sq_nonneg ε)
  have hQ0 : 0 ≤ (Q.card : ℝ) := by positivity
  nlinarith

/-- Complete numerical interface from exact Kazhdan repair to the finite
cluster machinery.  The three strict hypotheses are stated entirely in
terms of the input partial arrow and its original labelled commutation
defect.  They imply simultaneously that the repaired crossing is a
low-defect candidate and that it lies inside the required radius. -/
theorem repair_isClusterCandidate_and_close_of_bounds
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (hε : 0 < ε)
    (σY : G →* Equiv.Perm Y) (σZ : G →* Equiv.Perm Z)
    (b : FinitePartialBijection Y Z) {h : ℝ} {m : ℕ}
    (hclose :
      ε ^ 2 * (b.sourceDefect + b.targetDefect : ℕ) +
          16 * (totalCommutationDefect
            (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * ((2 * m : ℕ) : ℝ))
    (hforward :
      2 * (Q.card : ℝ) *
          (ε ^ 2 * (b.sourceDefect : ℝ) +
            8 * (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * (h * m / 2))
    (hbackward :
      2 * (Q.card : ℝ) *
          (ε ^ 2 * (b.targetDefect : ℝ) +
            8 * (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) <
        ε ^ 2 * (h * m / 2)) :
    (repair σY σZ b).IsClusterCandidate
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m ∧
      (repair σY σZ b).twoSidedDisagreement b < 2 * m := by
  let p := roundedDiagonalPermutation (sumActionHom σY σZ) b.swapPerm
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmissing := kazhdan_mul_missingMass_repair_le hQ σY σZ b
  have hselfScaled := hmissing.trans_lt hclose
  have hselfReal :
      (((repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect : ℕ) : ℝ) <
        ((2 * m : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_left hselfScaled hεsq.le
  have hself :
      (repair σY σZ b).sourceDefect +
          (repair σY σZ b).targetDefect < 2 * m := by
    exact_mod_cast hselfReal
  have hs := kazhdan_mul_sourceDefect_repair_le hQ σY σZ b
  have hfTag :=
    kazhdan_mul_card_taggedSumCommutationDefect_repaired_le hQ σY σZ b
  have hsMul := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * (Q.card : ℝ) by positivity)
  have hfCombined :
      ε ^ 2 *
          ((2 * (Fintype.card ↥Q * (repair σY σZ b).sourceDefect) +
            (sumCommutationDefect p
              (fun q : ↥Q ↦ σY q.1)
              (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) ≤
        2 * (Q.card : ℝ) *
            (ε ^ 2 * (b.sourceDefect : ℝ) +
              8 * (totalCommutationDefect
                (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
    simp only [Fintype.card_coe]
    push_cast
    dsimp only [p] at hfTag ⊢
    nlinarith
  have hfScaled := hfCombined.trans_lt hforward
  have hfReal :
      ((2 * (Fintype.card ↥Q * (repair σY σZ b).sourceDefect) +
        (sumCommutationDefect p
          (fun q : ↥Q ↦ σY q.1)
          (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) < h * m / 2 :=
    lt_of_mul_lt_mul_left hfScaled hεsq.le
  have ht := kazhdan_mul_targetDefect_repair_le hQ σY σZ b
  have hbTag :=
    kazhdan_mul_card_taggedSumCommutationDefect_repaired_inv_le
      hQ σY σZ b
  have htMul := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ 2 * (Q.card : ℝ) by positivity)
  have hbCombined :
      ε ^ 2 *
          ((2 * (Fintype.card ↥Q * (repair σY σZ b).targetDefect) +
            (sumCommutationDefect p⁻¹
              (fun q : ↥Q ↦ σY q.1)
              (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) ≤
        2 * (Q.card : ℝ) *
            (ε ^ 2 * (b.targetDefect : ℝ) +
              8 * (totalCommutationDefect
                (sumActionHom σY σZ) Q b.swapPerm : ℝ)) +
          8 * (Q.card : ℝ) ^ 2 *
            (totalCommutationDefect
              (sumActionHom σY σZ) Q b.swapPerm : ℝ) := by
    simp only [Fintype.card_coe]
    push_cast
    dsimp only [p] at hbTag ⊢
    nlinarith
  have hbScaled := hbCombined.trans_lt hbackward
  have hbReal :
      ((2 * (Fintype.card ↥Q * (repair σY σZ b).targetDefect) +
        (sumCommutationDefect p⁻¹
          (fun q : ↥Q ↦ σY q.1)
          (fun q : ↥Q ↦ σZ q.1)).card : ℕ) : ℝ) < h * m / 2 :=
    lt_of_mul_lt_mul_left hbScaled hεsq.le
  have hcand :
      (extractCrossing p).IsClusterCandidate
        (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1) h m :=
    isClusterCandidate_extractCrossing_of_bounds p
      (fun q : ↥Q ↦ σY q.1) (fun q : ↥Q ↦ σZ q.1)
      (by simpa only [repair, p] using hself)
      (by simpa only [repair, p] using hfReal)
      (by simpa only [repair, p] using hbReal)
  have hdist := kazhdan_mul_twoSidedDisagreement_repair_le hQ σY σZ b
  have hdistScaled := hdist.trans_lt hclose
  have hdistReal :
      (b.twoSidedDisagreement (repair σY σZ b) : ℝ) <
        ((2 * m : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_left hdistScaled hεsq.le
  have hdistNat : b.twoSidedDisagreement (repair σY σZ b) < 2 * m := by
    exact_mod_cast hdistReal
  refine ⟨?_, ?_⟩
  · simpa only [repair, p] using hcand
  · rw [twoSidedDisagreement_comm]
    exact hdistNat

end ExactPartialKazhdanRepair
end GroupApproximation
