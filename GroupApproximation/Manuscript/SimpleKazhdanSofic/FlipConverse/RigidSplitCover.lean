import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Rigid split, part 2: splitting rigid stabilizers from disjointness of supports

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").

Let `T`, `S` be minimal aperiodic homeomorphisms of Cantor spaces and
`Φ : [[T]] ≃* [[S]]` such that `Φ` and `Φ⁻¹` carry pairs of elements with disjoint moved sets
to pairs with disjoint moved sets.  For a clopen `U ⊆ X` there is a clopen `V ⊆ Y` with
`Φ F_U ⊆ F_V`, `Φ F_{Uᶜ} ⊆ F_{Vᶜ}` (`exists_split_of_disjoint`):

1. *Cover.*  Each `x ∈ U` is moved by some `f ∈ F_U` (`exists_supportedIn_apply_ne`); moved
   sets are open (`isClopen_movedSet`) and `U` is compact, so finitely many `f_i ∈ F_U` have
   moved sets covering `U`.  Put `V = ⋃ movedSet (Φ f_i)`, clopen.
2. `Φ F_{Uᶜ} ⊆ F_{Vᶜ}`: for `k ∈ F_{Uᶜ}`, `movedSet k` is disjoint from `movedSet f_i ⊆ U`,
   hence `movedSet (Φ k)` is disjoint from every `movedSet (Φ f_i)`.
3. `Φ F_U ⊆ F_V`: let `f ∈ F_U` and `N = movedSet (Φ f) \ V` (open).  If `σ ∈ [[S]]` is
   supported in `N`, then `movedSet σ` is disjoint from each `movedSet (Φ f_i) ⊆ V`, so
   `g = Φ⁻¹ σ` has moved set disjoint from each `movedSet f_i`, hence from `U`: `g ∈ F_{Uᶜ}`
   commutes with `f`, and `σ` commutes with `Φ f`.  By `supportedIn_compl_of_forall_commute`,
   `Φ f` fixes `N` pointwise; as `N ⊆ movedSet (Φ f)`, `N = ∅`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

theorem exists_split_of_disjoint {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X]
    [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y]
    {T : X ≃ₜ X} {S : Y ≃ₜ Y} (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S)
    (hTa : IsAperiodic T) (hSa : IsAperiodic S)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S)
    (hΦ : ∀ f k : topologicalFullGroup T,
      Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) →
        Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
          (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y)))
    (hΦs : ∀ f k : topologicalFullGroup S,
      Disjoint (movedSet (f : Y ≃ₜ Y)) (movedSet (k : Y ≃ₜ Y)) →
        Disjoint (movedSet ((Φ.symm f : topologicalFullGroup T) : X ≃ₜ X))
          (movedSet ((Φ.symm k : topologicalFullGroup T) : X ≃ₜ X)))
    {U : Set X} (hU : IsClopen U) :
    ∃ V : Set Y, IsClopen V ∧
      (∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) U →
        SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) V) ∧
      ∀ g : topologicalFullGroup T, SupportedIn (g : X ≃ₜ X) Uᶜ →
        SupportedIn ((Φ g : topologicalFullGroup S) : Y ≃ₜ Y) Vᶜ := by
  have hcov : U ⊆ ⋃ i : {f : topologicalFullGroup T // SupportedIn (f : X ≃ₜ X) U},
      movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X) := by
    intro x hx
    obtain ⟨g, hg, hgU, hgx⟩ := exists_supportedIn_apply_ne hT hU.isOpen hx
    exact Set.mem_iUnion.2 ⟨⟨⟨g, hg⟩, hgU⟩, hgx⟩
  obtain ⟨t, ht⟩ := hU.isClosed.isCompact.elim_finite_subcover
    (fun i : {f : topologicalFullGroup T // SupportedIn (f : X ≃ₜ X) U} =>
      movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X))
    (fun i => (isClopen_movedSet hTa i.1.2).isOpen) hcov
  have hV : IsClopen (⋃ i ∈ t, movedSet ((Φ i.1 : topologicalFullGroup S) : Y ≃ₜ Y)) :=
    isClopen_biUnion_finset fun i _ => isClopen_movedSet hSa (Φ i.1).2
  refine ⟨⋃ i ∈ t, movedSet ((Φ i.1 : topologicalFullGroup S) : Y ≃ₜ Y), hV, ?_, ?_⟩
  · intro f hf
    have hN : IsOpen (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y) ∩
        (⋃ i ∈ t, movedSet ((Φ i.1 : topologicalFullGroup S) : Y ≃ₜ Y))ᶜ) :=
      (isClopen_movedSet hSa (Φ f).2).isOpen.inter hV.isClosed.isOpen_compl
    have hfix : SupportedIn ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y)
        (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y) ∩
          (⋃ i ∈ t, movedSet ((Φ i.1 : topologicalFullGroup S) : Y ≃ₜ Y))ᶜ)ᶜ := by
      refine supportedIn_compl_of_forall_commute
        (h := ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y)) hS hN fun σ hσ hσN => ?_
      have hgU :
          SupportedIn ((Φ.symm ⟨σ, hσ⟩ : topologicalFullGroup T) : X ≃ₜ X) Uᶜ := by
        refine supportedIn_iff_movedSet_subset.2 fun x hx =>
          (Set.mem_compl_iff _ _).2 fun hxU => ?_
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hxU)
        have hd : Disjoint (movedSet ((Φ i.1 : topologicalFullGroup S) : Y ≃ₜ Y))
            (movedSet σ) := by
          refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
          have hy3 := supportedIn_iff_movedSet_subset.1 hσN hy2
          exact (Set.mem_compl_iff _ _).1 hy3.2 (Set.mem_iUnion₂.2 ⟨i, hi, hy1⟩)
        have hd' := hΦs (Φ i.1) ⟨σ, hσ⟩ hd
        rw [MulEquiv.symm_apply_apply] at hd'
        exact Set.disjoint_left.1 hd' hxi hx
      have hsub : f * Φ.symm ⟨σ, hσ⟩ = Φ.symm ⟨σ, hσ⟩ * f :=
        Subtype.ext (hf.commute_of_compl hgU)
      have hcomm' : Φ (f * Φ.symm ⟨σ, hσ⟩) = Φ (Φ.symm ⟨σ, hσ⟩ * f) := by
        rw [hsub]
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at hcomm'
      exact congrArg Subtype.val hcomm'
    refine supportedIn_iff_movedSet_subset.2 fun y hy => ?_
    by_contra hyV
    have hy' : ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y) y ≠ y := hy
    exact hy' (hfix y (Set.notMem_compl_iff.2 ⟨hy, hyV⟩))
  · intro k hk
    refine supportedIn_iff_movedSet_subset.2 fun y hy =>
      (Set.mem_compl_iff _ _).2 fun hyV => ?_
    obtain ⟨i, -, hyi⟩ := Set.mem_iUnion₂.1 hyV
    have hd : Disjoint (movedSet ((i.1 : topologicalFullGroup T) : X ≃ₜ X))
        (movedSet (k : X ≃ₜ X)) := by
      refine Set.disjoint_left.2 fun x hx1 hx2 => ?_
      exact (Set.mem_compl_iff _ _).1 (supportedIn_iff_movedSet_subset.1 hk hx2)
        (supportedIn_iff_movedSet_subset.1 i.2 hx1)
    exact Set.disjoint_left.1 (hΦ i.1 k hd) hyi hy

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_split_of_disjoint
