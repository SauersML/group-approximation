import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialRealize
import GroupApproximation.Meta.AxiomGuard

/-!
# Spatial realization, part 4: centralizers of rigid stabilizers

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").

For a minimal homeomorphism `T` of a Cantor space and a clopen `U ⊆ X`, the centralizer in `[[T]]`
of the rigid stabilizer `F_U = {g | SupportedIn g U}` is `F_{Uᶜ}`:

* `SupportedIn.commute_of_compl`: elements supported in `U` and in `Uᶜ` commute (each one maps
  its support set into itself, `SupportedIn.apply_mem`).
* `supportedIn_compl_of_forall_commute`: if a homeomorphism `h` commutes with every element of
  `[[T]]` supported in the open set `U`, then `h` fixes `U` pointwise.  If `h x ≠ x` for `x ∈ U`,
  separate `x`, `h x` by disjoint opens `A`, `B`; an element `σ ∈ [[T]]` supported in
  `W = U ∩ A ∩ h⁻¹ B` moves some `z ∈ W` (`exists_supportedIn_ne_one`), but `h z ∉ W` gives
  `h (σ z) = σ (h z) = h z`, so `σ z = z`.

Consequently (`rigidStabilizerTransport_of_rigidStabilizerSplit`) the remaining gap
`RigidStabilizerTransportStatement` is reduced to the strictly weaker
`RigidStabilizerSplitStatement`: for each clopen `U` there is a clopen `V` with
`Φ F_U ⊆ F_V` and `Φ F_{Uᶜ} ⊆ F_{Vᶜ}`.  Indeed if `Φ g ∈ F_V`, then `Φ g` commutes with
`Φ F_{Uᶜ} ⊆ F_{Vᶜ}`, so `g` commutes with `F_{Uᶜ}`, so `g ∈ F_{Uᶜᶜ} = F_U`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

section Centralizer

variable {X : Type*} [TopologicalSpace X]

/-- An element supported in `U` maps `U` into itself. -/
theorem SupportedIn.apply_mem {g : X ≃ₜ X} {U : Set X} (hg : SupportedIn g U) {x : X}
    (hx : x ∈ U) : g x ∈ U := by
  by_contra hgx
  have h1 : g (g x) = g x := hg (g x) hgx
  have h2 : g x = x := g.injective h1
  exact hgx (by rw [h2]; exact hx)

/-- Elements supported in complementary sets commute. -/
theorem SupportedIn.commute_of_compl {g k : X ≃ₜ X} {U : Set X} (hg : SupportedIn g U)
    (hk : SupportedIn k Uᶜ) : g * k = k * g := by
  refine Homeomorph.ext fun x => ?_
  show g (k x) = k (g x)
  by_cases hx : x ∈ U
  · have hkx : k x = x := hk x (Set.notMem_compl_iff.2 hx)
    have hkgx : k (g x) = g x := hk (g x) (Set.notMem_compl_iff.2 (hg.apply_mem hx))
    rw [hkx, hkgx]
  · have hgx : g x = x := hg x hx
    have hxc : x ∈ Uᶜ := Set.mem_compl hx
    have hkx : k x ∈ Uᶜ := hk.apply_mem hxc
    have hgkx : g (k x) = k x := hg (k x) ((Set.mem_compl_iff U (k x)).1 hkx)
    rw [hgx, hgkx]

/-- A homeomorphism commuting with every element of `[[T]]` supported in an open set `U` fixes
`U` pointwise. -/
theorem supportedIn_compl_of_forall_commute [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {U : Set X} (hU : IsOpen U) {h : X ≃ₜ X}
    (hc : ∀ σ ∈ topologicalFullGroup T, SupportedIn σ U → h * σ = σ * h) :
    SupportedIn h Uᶜ := by
  intro x hx
  have hxU : x ∈ U := Set.notMem_compl_iff.1 hx
  by_contra hne
  have hne' : x ≠ h x := fun he => hne he.symm
  obtain ⟨A, B, hA, hB, hxA, hhxB, hAB⟩ := t2_separation hne'
  have hW : IsOpen (U ∩ A ∩ h ⁻¹' B) := (hU.inter hA).inter (hB.preimage h.continuous)
  obtain ⟨σ, hσ, hσW, z, hz⟩ := exists_supportedIn_ne_one hT hW ⟨x, ⟨hxU, hxA⟩, hhxB⟩
  have hzW : z ∈ U ∩ A ∩ h ⁻¹' B := by
    by_contra hzW
    exact hz (hσW z hzW)
  have hhzB : h z ∈ B := hzW.2
  have hhz : h z ∉ U ∩ A ∩ h ⁻¹' B := fun hmem => Set.disjoint_left.1 hAB hmem.1.2 hhzB
  have h1 : σ (h z) = h z := hσW (h z) hhz
  have hcomm : h * σ = σ * h := hc σ hσ (hσW.mono fun y hy => hy.1.1)
  have h2 : h (σ z) = σ (h z) := DFunLike.congr_fun hcomm z
  exact hz (h.injective (h2.trans h1))

end Centralizer

/-- Isomorphisms of topological full groups of Cantor minimal systems split rigid stabilizers of
complementary clopen sets into rigid stabilizers of complementary clopen sets:
`Φ F_U ⊆ F_V` and `Φ F_{Uᶜ} ⊆ F_{Vᶜ}` for some clopen `V`. -/
def RigidStabilizerSplitStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ U : Set X, IsClopen U →
        ∃ V : Set Y, IsClopen V ∧
          (∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) U →
            SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V) ∧
          ∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) Uᶜ →
            SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) Vᶜ

/-- The two inclusions `Φ F_U ⊆ F_V`, `Φ F_{Uᶜ} ⊆ F_{Vᶜ}` force `Φ F_U = F_V`. -/
theorem supportedIn_iff_of_split {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X]
    {T : X ≃ₜ X} {S : Y ≃ₜ Y} (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsClopen U)
    {V : Set Y}
    (h1 : ∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) U →
      SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V)
    (h2 : ∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) Uᶜ →
      SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) Vᶜ)
    (g : topologicalFullGroup T) :
    SupportedIn (g : X ≃ₜ X) U ↔ SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V := by
  refine ⟨h1 g, fun hg => ?_⟩
  have hc : SupportedIn (g : X ≃ₜ X) Uᶜᶜ := by
    refine supportedIn_compl_of_forall_commute hT hU.isClosed.isOpen_compl fun σ hσ hσU => ?_
    have hΦ := hg.commute_of_compl (h2 ⟨σ, hσ⟩ hσU)
    have hΦ' : Φ (g * (⟨σ, hσ⟩ : topologicalFullGroup T)) =
        Φ ((⟨σ, hσ⟩ : topologicalFullGroup T) * g) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hΦ
    exact congrArg Subtype.val (Φ.injective hΦ')
  rwa [compl_compl] at hc

/-- Reduction of the transport of rigid stabilizers to the split statement. -/
theorem rigidStabilizerTransport_of_rigidStabilizerSplit
    (hsplit : RigidStabilizerSplitStatement) : RigidStabilizerTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ U hU => by
    obtain ⟨V, hV, h1, h2⟩ := hsplit X Y T S hT hS Φ U hU
    exact ⟨V, hV, supportedIn_iff_of_split hT Φ hU h1 h2⟩

/-- The printed converse for topological full groups, reduced to `RigidStabilizerSplitStatement`. -/
theorem manuscriptSentence_flipConjugateConverse_of_rigidStabilizerSplit
    (hsplit : RigidStabilizerSplitStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_rigidStabilizerTransport
    (rigidStabilizerTransport_of_rigidStabilizerSplit hsplit) hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SupportedIn.apply_mem
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SupportedIn.commute_of_compl
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_compl_of_forall_commute
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidStabilizerSplitStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_iff_of_split
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabilizerTransport_of_rigidStabilizerSplit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_rigidStabilizerSplit
