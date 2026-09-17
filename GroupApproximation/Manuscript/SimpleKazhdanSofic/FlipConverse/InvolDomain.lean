import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolDomainStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution normal form, part 2: a clopen fundamental domain for an involution

Lane sk-flip-11 (Bezuglyi–Medynets involution normal form), census row `2e7c7d9ab149`
(tex: "for topological full groups the converse holds"; absent from current tex).

Let `X` be compact, Hausdorff and totally disconnected, and let `σ` be an involutive
homeomorphism (`σ * σ = 1`) whose moved set `movedSet σ = {x | σ x ≠ x}` is closed. Then there is
a clopen `V` with `V ∩ σ V = ∅` and `movedSet σ = V ∪ σ V`
(`exists_fundamentalDomain_of_isClosed_movedSet`).

For `T` aperiodic and `σ ∈ [[T]]`, `movedSet σ` is clopen by `isClopen_movedSet`
(`exists_fundamentalDomain_of_involution_of_isAperiodic`). A minimal homeomorphism of a nonempty
perfect Hausdorff space is aperiodic (`isAperiodic_of_isMinimalHomeo`, `infinite_of_perfectSpace`),
which gives `exists_fundamentalDomain_of_involution` for the Cantor minimal package.

Route.
1. A local copy of lane sk-flip-01 with `f = k = σ`: a moved point `x` has a clopen neighbourhood
   `W` with `W ∩ σ W = ∅` (`exists_isClopen_displaced_of_apply_ne`).
2. `movedSet σ` is closed, hence compact. It is covered by finitely many such `W`.
3. The greedy step (`exists_displaced_clopen_saturating_finset`) produces a displaced clopen `V`
   whose saturation `V ∪ σ⁻¹ V` contains the cover. Since `σ` is an involution, `σ '' V = σ⁻¹' V`.
4. A displaced set and its image consist of moved points, which gives the reverse inclusion.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A point moved by a homeomorphism has a clopen neighbourhood displaced by it. -/
theorem exists_isClopen_displaced_of_apply_ne [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {σ : X ≃ₜ X} {x : X} (hx : σ x ≠ x) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ ∀ z ∈ W, σ z ∉ W := by
  obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := t2_separation hx.symm
  have hO : IsOpen (A ∩ σ ⁻¹' B) := hA.inter (hB.preimage σ.continuous)
  have hxO : x ∈ A ∩ σ ⁻¹' B := ⟨hxA, hyB⟩
  obtain ⟨W, hWc, hxW, hWO⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 (hO.mem_nhds hxO)
  have hW : IsClopen W := hWc
  refine ⟨W, hW, hxW, fun z hz hz' => ?_⟩
  have h1 : σ z ∈ A := (hWO hz').1
  have h2 : σ z ∈ B := (hWO hz).2
  exact Set.disjoint_left.1 hAB h1 h2

/-- Clopen fundamental domain of an involutive homeomorphism with closed moved set. -/
theorem exists_fundamentalDomain_of_isClosed_movedSet [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {σ : X ≃ₜ X} (h2 : σ * σ = 1)
    (hclosed : IsClosed (movedSet σ)) :
    ∃ V : Set X, IsClopen V ∧ Disjoint V (σ '' V) ∧ movedSet σ = V ∪ σ '' V := by
  have hs : ∀ z, σ (σ z) = z := fun z => by
    show (σ * σ) z = z
    rw [h2, Homeomorph.one_apply]
  have hinv : Function.LeftInverse (⇑σ) (⇑σ) := hs
  have himg : ∀ S : Set X, σ '' S = σ ⁻¹' S := fun S =>
    congrFun (Set.image_eq_preimage_of_inverse hinv hinv) S
  have hex : ∀ x : X, ∃ W : Set X,
      IsClopen W ∧ (∀ z ∈ W, σ z ∉ W) ∧ (x ∈ movedSet σ → x ∈ W) := by
    intro x
    by_cases hx : σ x = x
    · refine ⟨∅, isClopen_empty, fun z hz => absurd hz (Set.notMem_empty z), fun hxm => ?_⟩
      have hxm' : σ x ≠ x := hxm
      exact absurd hx hxm'
    · obtain ⟨W, hW, hxW, hWd⟩ := exists_isClopen_displaced_of_apply_ne hx
      exact ⟨W, hW, hWd, fun _ => hxW⟩
  choose U hUc hUd hUx using hex
  obtain ⟨t, -, hcover⟩ := hclosed.isCompact.elim_nhds_subcover U
    (fun x hx => (hUc x).isOpen.mem_nhds (hUx x hx))
  obtain ⟨V, hVc, hVd, hVU⟩ := exists_displaced_clopen_saturating_finset hs hUc hUd t
  refine ⟨V, hVc, ?_, ?_⟩
  · rw [himg V]
    exact Set.disjoint_left.2 fun z hz hz' => hVd z hz hz'
  · rw [himg V]
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.1 (hcover hz)
      exact hVU x hxt hzx
    · intro z hz
      show σ z ≠ z
      intro hfix
      rcases (Set.mem_union _ _ _).1 hz with hzV | hszV
      · have hszV : σ z ∈ V := by
          rw [hfix]
          exact hzV
        exact hVd z hzV hszV
      · have hzV : z ∈ V := by
          have hszV' : σ z ∈ V := hszV
          rw [hfix] at hszV'
          exact hszV'
        exact hVd z hzV hszV

/-- Clopen fundamental domain of an involution of `[[T]]`, for aperiodic `T`. -/
theorem exists_fundamentalDomain_of_involution_of_isAperiodic [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {T σ : X ≃ₜ X} (hT : IsAperiodic T)
    (hσ : σ ∈ topologicalFullGroup T) (h2 : σ * σ = 1) :
    ∃ V : Set X, IsClopen V ∧ Disjoint V (σ '' V) ∧ movedSet σ = V ∪ σ '' V :=
  exists_fundamentalDomain_of_isClosed_movedSet h2 (isClopen_movedSet hT hσ).isClosed

/-- Bezuglyi–Medynets involution normal form (Cantor minimal package): an involution `σ` of the
topological full group `[[T]]` of a minimal homeomorphism `T` of a nonempty perfect compact
Hausdorff totally disconnected space has a clopen fundamental domain `V`, so that
`movedSet σ = V ⊔ σ V`. -/
theorem exists_fundamentalDomain_of_involution [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {σ : X ≃ₜ X} (hσ : σ ∈ topologicalFullGroup T) (h2 : σ * σ = 1) :
    ∃ V : Set X, IsClopen V ∧ Disjoint V (σ '' V) ∧ movedSet σ = V ∪ σ '' V := by
  haveI : Infinite X := infinite_of_perfectSpace
  exact exists_fundamentalDomain_of_involution_of_isAperiodic
    (isAperiodic_of_isMinimalHomeo hT) hσ h2

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_displaced_of_apply_ne
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_fundamentalDomain_of_isClosed_movedSet
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_fundamentalDomain_of_involution_of_isAperiodic
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_fundamentalDomain_of_involution
