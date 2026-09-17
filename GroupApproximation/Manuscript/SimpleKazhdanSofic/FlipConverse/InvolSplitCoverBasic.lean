import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Involutive split cover, part 1: involution-only tools

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"); lane
`sk-flip-09`.

* `InvolutionApplyNeStatement`: the interface of lane `sk-flip-08`
  (`exists_involution_supportedIn_apply_ne`, not yet on disk): every point `x` of an open set `W`
  is moved by an *involution* of `[[T]]` supported in `W`.  It is TRUE: the witness of the corpus
  lemma `exists_supportedIn_apply_ne` is `swapFun T V n`, an involution by `swapFun_involutive`.
  Lane 08's theorem proves this Statement by `fun X _ _ _ _ _ T hT W hW x hx =>
  exists_involution_supportedIn_apply_ne hT hW hx`.  Lane 08's second lemma
  (`exists_involution_supportedIn_ne_one`) is not needed here.
* `supportedIn_compl_of_forall_involution_commute`: a homeomorphism commuting with every
  *involution* of `[[T]]` supported in the open set `U` fixes `U` pointwise.  If `h x ≠ x` with
  `x ∈ U`, separate `x`, `h x` by disjoint opens `A`, `B`; an involution `σ` supported in
  `W = U ∩ A ∩ h⁻¹ B` moves `x`, while `h x ∉ W` gives `h (σ x) = σ (h x) = h x`, so `σ x = x`.
* `exists_involution_cover`: a clopen `U` is covered by the moved sets of finitely many
  involutions of `[[T]]` supported in `U` (compactness plus clopen moved sets).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

universe u

/-- Interface of lane `sk-flip-08`: every point of an open set of a Cantor minimal system is moved
by an involution of `[[T]]` supported in that set. -/
def InvolutionApplyNeStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] (T : X ≃ₜ X), IsMinimalHomeo T → ∀ W : Set X, IsOpen W → ∀ x ∈ W,
      ∃ g ∈ topologicalFullGroup T, g * g = 1 ∧ SupportedIn g W ∧ g x ≠ x

/-- A homeomorphism commuting with every involution of `[[T]]` supported in an open set `U`
fixes `U` pointwise. -/
theorem supportedIn_compl_of_forall_involution_commute (h08 : InvolutionApplyNeStatement.{u})
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {U : Set X} (hU : IsOpen U)
    {h : X ≃ₜ X}
    (hc : ∀ σ ∈ topologicalFullGroup T, σ * σ = 1 → SupportedIn σ U → h * σ = σ * h) :
    SupportedIn h Uᶜ := by
  intro x hx
  have hxU : x ∈ U := Set.notMem_compl_iff.1 hx
  by_contra hne
  have hne' : x ≠ h x := fun he => hne he.symm
  obtain ⟨A, B, hA, hB, hxA, hhxB, hAB⟩ := t2_separation hne'
  have hW : IsOpen (U ∩ A ∩ h ⁻¹' B) := (hU.inter hA).inter (hB.preimage h.continuous)
  obtain ⟨σ, hσ, hσ2, hσW, hσx⟩ := h08 X T hT _ hW x ⟨⟨hxU, hxA⟩, hhxB⟩
  have hhx : h x ∉ U ∩ A ∩ h ⁻¹' B := fun hmem => Set.disjoint_left.1 hAB hmem.1.2 hhxB
  have h1 : σ (h x) = h x := hσW (h x) hhx
  have hcomm : h * σ = σ * h := hc σ hσ hσ2 (hσW.mono fun y hy => hy.1.1)
  have h2 : h (σ x) = σ (h x) := DFunLike.congr_fun hcomm x
  exact hσx (h.injective (h2.trans h1))

/-- A clopen set is covered by the moved sets of finitely many involutions of `[[T]]` supported
in it. -/
theorem exists_involution_cover (h08 : InvolutionApplyNeStatement.{u}) {X : Type u}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) (hTa : IsAperiodic T) {U : Set X}
    (hU : IsClopen U) :
    ∃ t : Finset {f : topologicalFullGroup T // f * f = 1 ∧ SupportedIn (f : X ≃ₜ X) U},
      U ⊆ ⋃ i ∈ t, movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X) := by
  have hcov : U ⊆ ⋃ i : {f : topologicalFullGroup T // f * f = 1 ∧ SupportedIn (f : X ≃ₜ X) U},
      movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X) := by
    intro x hx
    obtain ⟨g, hg, hg2, hgU, hgx⟩ := h08 X T hT U hU.isOpen x hx
    exact Set.mem_iUnion.2 ⟨⟨⟨g, hg⟩, Subtype.ext hg2, hgU⟩, hgx⟩
  exact hU.isClosed.isCompact.elim_finite_subcover
    (fun i : {f : topologicalFullGroup T // f * f = 1 ∧ SupportedIn (f : X ≃ₜ X) U} =>
      movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X))
    (fun i => (isClopen_movedSet hTa i.1.2).isOpen) hcov

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolutionApplyNeStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_compl_of_forall_involution_commute
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_involution_cover
