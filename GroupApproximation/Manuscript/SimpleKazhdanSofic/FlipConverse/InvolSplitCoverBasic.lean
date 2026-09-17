import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolSmall
import GroupApproximation.Meta.AxiomGuard

/-!
# Involutive split cover, part 1: involution-only tools

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Lane `sk-flip-09`.

Both lemmas use lane 08's `exists_involution_supportedIn_apply_ne` (`InvolSmall.lean`): every
point `x` of an open set `W` is moved by an involution of `[[T]]` supported in `W`.

* `supportedIn_compl_of_forall_involution_commute`: a homeomorphism commuting with every
  *involution* of `[[T]]` supported in the open set `U` fixes `U` pointwise.  If `h x ≠ x` with
  `x ∈ U`, separate `x`, `h x` by disjoint opens `A`, `B`.  An involution `σ` supported in
  `W = U ∩ A ∩ h⁻¹ B` moves `x`, while `h x ∉ W` gives `h (σ x) = σ (h x) = h x`, so `σ x = x`.
  This is the involution-only variant of `supportedIn_compl_of_forall_commute`
  (`RigidCentralizer.lean`).
* `exists_involution_cover`: a clopen `U` is covered by the moved sets of finitely many
  involutions of `[[T]]` supported in `U` (compactness plus clopen moved sets).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- A homeomorphism commuting with every involution of `[[T]]` supported in an open set `U`
fixes `U` pointwise. -/
theorem supportedIn_compl_of_forall_involution_commute [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {U : Set X} (hU : IsOpen U) {h : X ≃ₜ X}
    (hc : ∀ σ ∈ topologicalFullGroup T, σ * σ = 1 → SupportedIn σ U → h * σ = σ * h) :
    SupportedIn h Uᶜ := by
  intro x hx
  have hxU : x ∈ U := Set.notMem_compl_iff.1 hx
  by_contra hne
  have hne' : x ≠ h x := fun he => hne he.symm
  obtain ⟨A, B, hA, hB, hxA, hhxB, hAB⟩ := t2_separation hne'
  have hW : IsOpen (U ∩ A ∩ h ⁻¹' B) := (hU.inter hA).inter (hB.preimage h.continuous)
  have hxW : x ∈ U ∩ A ∩ h ⁻¹' B := ⟨⟨hxU, hxA⟩, hhxB⟩
  obtain ⟨σ, hσ, hσ2, hσW, hσx⟩ := exists_involution_supportedIn_apply_ne hT hW hxW
  have hhx : h x ∉ U ∩ A ∩ h ⁻¹' B := fun hmem => Set.disjoint_left.1 hAB hmem.1.2 hhxB
  have h1 : σ (h x) = h x := hσW (h x) hhx
  have hcomm : h * σ = σ * h := hc σ hσ hσ2 (hσW.mono fun y hy => hy.1.1)
  have h2 : h (σ x) = σ (h x) := DFunLike.congr_fun hcomm x
  exact hσx (h.injective (h2.trans h1))

/-- A clopen set is covered by the moved sets of finitely many involutions of `[[T]]` supported
in it. -/
theorem exists_involution_cover [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) (hTa : IsAperiodic T) {U : Set X}
    (hU : IsClopen U) :
    ∃ t : Finset {f : topologicalFullGroup T // f * f = 1 ∧ SupportedIn (f : X ≃ₜ X) U},
      U ⊆ ⋃ i ∈ t, movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X) := by
  have hcov : U ⊆ ⋃ i : {f : topologicalFullGroup T // f * f = 1 ∧ SupportedIn (f : X ≃ₜ X) U},
      movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X) := by
    intro x hx
    obtain ⟨g, hg, hg2, hgU, hgx⟩ := exists_involution_supportedIn_apply_ne hT hU.isOpen hx
    have hg2' : (⟨g, hg⟩ : topologicalFullGroup T) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
    exact Set.mem_iUnion.2 ⟨⟨⟨g, hg⟩, hg2', hgU⟩, hgx⟩
  exact hU.isClosed.isCompact.elim_finite_subcover
    (fun i : {f : topologicalFullGroup T // f * f = 1 ∧ SupportedIn (f : X ≃ₜ X) U} =>
      movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X))
    (fun i => (isClopen_movedSet hTa i.1.2).isOpen) hcov

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_compl_of_forall_involution_commute
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_involution_cover
