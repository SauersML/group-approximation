import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Profinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Flip converse infrastructure: a clopen set displaced by two homeomorphisms

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no line number).  Lane `sk-flip-01`.

* `exists_isClopen_displaced_common`: on a compact Hausdorff totally disconnected space, if `x`
  is moved by both `f` and `k`, then some clopen `W ∋ x` is disjoint from `f '' W` and `k '' W`.
* `exists_isClopen_displaced`: the special case `f = k`.

Route: separate `x` from `f x` by disjoint opens `A`, `B`, and `x` from `k x` by disjoint opens
`C`, `D`.  The open set `A ∩ C ∩ (f⁻¹ B ∩ k⁻¹ D)` contains `x`.  It contains a clopen `W ∋ x`
(`isTopologicalBasis_isClopen`).  A point `f w` with `w ∈ W` lies in `B`, so it is not in `W ⊆ A`.
The argument for `k` is the same.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A point moved by two homeomorphisms has a clopen neighbourhood displaced by both. -/
theorem exists_isClopen_displaced_common [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] {f k : X ≃ₜ X} {x : X} (hf : f x ≠ x) (hk : k x ≠ x) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ Disjoint W (f '' W) ∧ Disjoint W (k '' W) := by
  obtain ⟨A, B, hA, hB, hxA, hfxB, hAB⟩ := t2_separation hf.symm
  obtain ⟨C, D, hC, hD, hxC, hkxD, hCD⟩ := t2_separation hk.symm
  have hO : IsOpen (A ∩ C ∩ (f ⁻¹' B ∩ k ⁻¹' D)) :=
    (hA.inter hC).inter ((hB.preimage f.continuous).inter (hD.preimage k.continuous))
  have hxO : x ∈ A ∩ C ∩ (f ⁻¹' B ∩ k ⁻¹' D) := ⟨⟨hxA, hxC⟩, hfxB, hkxD⟩
  obtain ⟨W, hWc, hxW, hWO⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 (hO.mem_nhds hxO)
  have hW : IsClopen W := hWc
  refine ⟨W, hW, hxW, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro z hzW ⟨w, hwW, rfl⟩
    have h1 : f w ∈ A := (hWO hzW).1.1
    have h2 : f w ∈ B := (hWO hwW).2.1
    exact Set.disjoint_left.1 hAB h1 h2
  · rw [Set.disjoint_left]
    rintro z hzW ⟨w, hwW, rfl⟩
    have h1 : k w ∈ C := (hWO hzW).1.2
    have h2 : k w ∈ D := (hWO hwW).2.2
    exact Set.disjoint_left.1 hCD h1 h2

/-- A point moved by a homeomorphism has a clopen neighbourhood displaced by it. -/
theorem exists_isClopen_displaced [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {f : X ≃ₜ X} {x : X} (hf : f x ≠ x) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ Disjoint W (f '' W) := by
  obtain ⟨W, hW, hxW, hWf, -⟩ := exists_isClopen_displaced_common hf hf
  exact ⟨W, hW, hxW, hWf⟩

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_displaced_common
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_isClopen_displaced
