import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraTowerBase
import GroupApproximation.Meta.AxiomGuard

/-!
# Flip converse infrastructure (lane sk-flip-03, part 2): towers inside an open set

Corrected form of the lane target (the consecutive-levels version is false, see
`InfraTowerBase`): for a minimal homeomorphism `T` of a compact Hausdorff totally disconnected
perfect space and a nonempty open `W`, for every `n` there are a nonempty clopen `V` and `n`
distinct exponents `k i ∈ ℤ` such that the levels `T^{k i} V` lie in `W` and are pairwise
disjoint.  This is what the lane-05 embedding of `S_n` supported in `W` needs (with the levels
`T^{k i} V` in place of `T^i V`).

Proof.
* `infinite_setOf_zpow_apply_mem`: for every `x`, `{m | T^m x ∈ W}` is infinite.  Otherwise the
  orbit points in `W` form a finite set `F`; `W` is an open set in a perfect T₁ space, hence
  infinite (`infinite_of_mem_nhds`), so `W \ F` is a nonempty open set, and by density of the
  orbit it contains some `T^m x`, which then lies in `F`: contradiction.
* Pick `x ∈ W`, an injective `k : Fin n → ℤ` with values in that set (`Set.Infinite.natEmbedding`)
  and apply `exists_isClopen_tower_of_exponents` (aperiodicity from
  `isAperiodic_of_isMinimalHomeo`, infiniteness from `infinite_of_perfectSpace`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A dense orbit returns infinitely often to a nonempty open subset of a perfect T₁ space. -/
theorem infinite_setOf_zpow_apply_mem [T1Space X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) (x : X) :
    {m : ℤ | (T ^ m) x ∈ W}.Infinite := by
  refine fun hfin => ?_
  obtain ⟨y, hy⟩ := hne
  have hF : ((fun m : ℤ => (T ^ m) x) '' {m : ℤ | (T ^ m) x ∈ W}).Finite := hfin.image _
  have hWinf : W.Infinite := infinite_of_mem_nhds y (hW.mem_nhds hy)
  obtain ⟨_, ⟨m, rfl⟩, hmW, hmF⟩ :=
    (hT x).exists_mem_open (hW.sdiff hF.isClosed) (hWinf.sdiff hF).nonempty
  exact hmF ⟨m, hmW, rfl⟩

/-- Corrected lane target: a clopen tower base whose `n` levels (at distinct, not necessarily
consecutive, exponents) lie inside a given nonempty open set and are pairwise disjoint. -/
theorem exists_isClopen_tower_in_open [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W)
    (hne : W.Nonempty) (n : ℕ) :
    ∃ V : Set X, ∃ k : Fin n → ℤ, Function.Injective k ∧ IsClopen V ∧ V.Nonempty ∧
      (∀ i, (T ^ k i) '' V ⊆ W) ∧ ∀ i j, i ≠ j → Disjoint ((T ^ k i) '' V) ((T ^ k j) '' V) := by
  obtain ⟨x, hx⟩ := hne
  haveI : Nonempty X := ⟨x⟩
  haveI : Infinite X := infinite_of_perfectSpace
  have hTa : IsAperiodic T := isAperiodic_of_isMinimalHomeo hT
  have hS : {m : ℤ | (T ^ m) x ∈ W}.Infinite := infinite_setOf_zpow_apply_mem hT hW ⟨x, hx⟩ x
  have hex : ∃ k : Fin n → ℤ, Function.Injective k ∧ ∀ i, (T ^ k i) x ∈ W :=
    ⟨fun i => ((hS.natEmbedding _) (i : ℕ)).1,
      fun i j h => Fin.ext ((hS.natEmbedding _).injective (Subtype.ext h)),
      fun i => ((hS.natEmbedding _) (i : ℕ)).2⟩
  obtain ⟨k, hk, hkx⟩ := hex
  obtain ⟨V, hV, hxV, -, hVW, hdisj⟩ :=
    exists_isClopen_tower_of_exponents hTa hk hW isOpen_univ (Set.mem_univ x) hkx
  exact ⟨V, k, hk, hV, ⟨x, hxV⟩, hVW, hdisj⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.infinite_setOf_zpow_apply_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_tower_in_open
