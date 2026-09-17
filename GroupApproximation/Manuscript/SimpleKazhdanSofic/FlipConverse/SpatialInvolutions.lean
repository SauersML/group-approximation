import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.FullGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Spatial realization, part 1: elements of `[[T]]` with small support

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").  Step 1 of
the Rubin/Matui route to `SpatialRealizationStatement`: a minimal homeomorphism of a Cantor space
has nontrivial elements of `[[T]]` supported in every nonempty open set.

* `SupportedIn g U`: `g` fixes every point outside `U`.
* `supportedIn_conj_iff`: `g m g⁻¹` is supported in `U` iff `m` is supported in `g⁻¹ U`.
* `exists_supportedIn_ne_one`: for `x ∈ W` open, perfectness and minimality give `n` with
  `T^n x ∈ W \ {x}`; a clopen `V ∋ x` with `V, T^n V ⊆ W` and `V ∩ T^n V = ∅` exists (clopen basis,
  Hausdorff), and the involution `σ = T^n` on `V`, `T^{-n}` on `T^n V`, `id` elsewhere lies in
  `[[T]]` (cocycle `swapCocycle`), is supported in `W` and moves `x`.
* `subset_of_forall_supportedIn`, `eq_of_forall_supportedIn_iff`: the rigid stabilizers
  `{g | SupportedIn g U}` determine clopen sets `U`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- `g` is supported in `U`: it fixes every point outside `U`. -/
def SupportedIn (g : X ≃ₜ X) (U : Set X) : Prop := ∀ x, x ∉ U → g x = x

theorem SupportedIn.mono {g : X ≃ₜ X} {U U' : Set X} (hg : SupportedIn g U) (hUU' : U ⊆ U') :
    SupportedIn g U' := fun x hx => hg x fun hxU => hx (hUU' hxU)

theorem supportedIn_conj_iff (g m : X ≃ₜ X) (U : Set X) :
    SupportedIn (g * m * g⁻¹) U ↔ SupportedIn m (g ⁻¹' U) := by
  constructor
  · intro h x hx
    have h1 : g (m (g.symm (g x))) = g x := h (g x) hx
    rw [Homeomorph.symm_apply_apply] at h1
    exact g.injective h1
  · intro h y hy
    have hy' : g.symm y ∉ g ⁻¹' U := by
      rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
      exact hy
    show g (m (g.symm y)) = y
    rw [h (g.symm y) hy', Homeomorph.apply_symm_apply]

open Classical in
/-- The cocycle of the involution exchanging `V` with `T^n V`. -/
noncomputable def swapCocycle (T : X ≃ₜ X) (V : Set X) (n : ℤ) (z : X) : ℤ :=
  if z ∈ V then n else if (T ^ (-n)) z ∈ V then -n else 0

/-- The involution exchanging `V` with `T^n V`. -/
noncomputable def swapFun (T : X ≃ₜ X) (V : Set X) (n : ℤ) (z : X) : X :=
  (T ^ swapCocycle T V n z) z

theorem swapCocycle_of_mem (T : X ≃ₜ X) {V : Set X} (n : ℤ) {z : X} (hz : z ∈ V) :
    swapCocycle T V n z = n := by
  classical
  rw [swapCocycle, if_pos hz]

theorem swapCocycle_of_notMem (T : X ≃ₜ X) {V : Set X} (n : ℤ) {z : X} (hz : z ∉ V)
    (hz' : (T ^ (-n)) z ∈ V) : swapCocycle T V n z = -n := by
  classical
  rw [swapCocycle, if_neg hz, if_pos hz']

theorem swapCocycle_of_notMem_notMem (T : X ≃ₜ X) {V : Set X} (n : ℤ) {z : X} (hz : z ∉ V)
    (hz' : (T ^ (-n)) z ∉ V) : swapCocycle T V n z = 0 := by
  classical
  rw [swapCocycle, if_neg hz, if_neg hz']

theorem continuous_swapCocycle (T : X ≃ₜ X) {V : Set X} (hV : IsClopen V) (n : ℤ) :
    Continuous (swapCocycle T V n) := by
  classical
  have hfr1 : frontier {z | z ∈ V} = ∅ := by
    rw [Set.setOf_mem_eq]
    exact isClopen_iff_frontier_eq_empty.1 hV
  have hfr2 : frontier {z | (T ^ (-n)) z ∈ V} = ∅ :=
    isClopen_iff_frontier_eq_empty.1 (hV.preimage (T ^ (-n)).continuous)
  refine Continuous.if (fun a ha => ?_) continuous_const
    (Continuous.if (fun a ha => ?_) continuous_const continuous_const)
  · have h0 : a ∈ (∅ : Set X) := by
      rw [← hfr1]
      exact ha
    exact absurd h0 (Set.notMem_empty a)
  · have h0 : a ∈ (∅ : Set X) := by
      rw [← hfr2]
      exact ha
    exact absurd h0 (Set.notMem_empty a)

theorem swapFun_involutive (T : X ≃ₜ X) {V : Set X} (n : ℤ)
    (hdisj : ∀ z ∈ V, (T ^ n) z ∉ V) (z : X) : swapFun T V n (swapFun T V n z) = z := by
  by_cases hz : z ∈ V
  · have h1 : swapFun T V n z = (T ^ n) z := by
      rw [swapFun, swapCocycle_of_mem T n hz]
    have h2 : (T ^ (-n)) ((T ^ n) z) = z := by
      rw [← homeoPow_add, neg_add_cancel, homeoPow_zero]
    have h3 : (T ^ (-n)) ((T ^ n) z) ∈ V := by
      rw [h2]
      exact hz
    rw [h1, swapFun, swapCocycle_of_notMem T n (hdisj z hz) h3, h2]
  · by_cases hz' : (T ^ (-n)) z ∈ V
    · have h1 : swapFun T V n z = (T ^ (-n)) z := by
        rw [swapFun, swapCocycle_of_notMem T n hz hz']
      have h2 : (T ^ n) ((T ^ (-n)) z) = z := by
        rw [← homeoPow_add, add_neg_cancel, homeoPow_zero]
      rw [h1, swapFun, swapCocycle_of_mem T n hz', h2]
    · have h1 : swapFun T V n z = z := by
        rw [swapFun, swapCocycle_of_notMem_notMem T n hz hz', homeoPow_zero]
      rw [h1, h1]

/-- Every nonempty open set supports a nontrivial element of `[[T]]` (an involution). -/
theorem exists_supportedIn_ne_one [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W)
    (hne : W.Nonempty) :
    ∃ g ∈ topologicalFullGroup T, SupportedIn g W ∧ ∃ x, g x ≠ x := by
  obtain ⟨x, hxW⟩ := hne
  obtain ⟨y, ⟨hyW, -⟩, hyx⟩ :=
    accPt_iff_nhds.1 (PerfectSpace.univ_preperfect x (Set.mem_univ x)) W (hW.mem_nhds hxW)
  obtain ⟨_, ⟨n, rfl⟩, hnW, hnx⟩ :=
    (hT x).exists_mem_open (hW.inter isOpen_compl_singleton) ⟨y, hyW, hyx⟩
  have hnW' : (T ^ n) x ∈ W := hnW
  have hnx' : (T ^ n) x ≠ x := hnx
  obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := t2_separation hnx'.symm
  have hO : IsOpen (W ∩ A ∩ (T ^ n) ⁻¹' (W ∩ B)) :=
    (hW.inter hA).inter ((hW.inter hB).preimage (T ^ n).continuous)
  have hxO : x ∈ W ∩ A ∩ (T ^ n) ⁻¹' (W ∩ B) := ⟨⟨hxW, hxA⟩, hnW', hyB⟩
  obtain ⟨V, hVc, hxV, hVO⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 (hO.mem_nhds hxO)
  have hV : IsClopen V := hVc
  have hdisj : ∀ z ∈ V, (T ^ n) z ∉ V := by
    intro z hz hz'
    have h1 : (T ^ n) z ∈ A := (hVO hz').1.2
    have h2 : (T ^ n) z ∈ B := (hVO hz).2.2
    exact Set.disjoint_left.1 hAB h1 h2
  have hinv : ∀ z, swapFun T V n (swapFun T V n z) = z := swapFun_involutive T n hdisj
  have hcont : Continuous (swapFun T V n) :=
    continuous_hpow_apply T (continuous_swapCocycle T hV n)
  refine ⟨⟨⟨swapFun T V n, swapFun T V n, hinv, hinv⟩, hcont, hcont⟩,
    mem_topologicalFullGroup.2 ⟨swapCocycle T V n, continuous_swapCocycle T hV n, fun z => rfl⟩,
    fun z hz => ?_, x, ?_⟩
  · have hzV : z ∉ V := fun h => hz (hVO h).1.1
    have hzV' : (T ^ (-n)) z ∉ V := by
      intro h
      have h1 : (T ^ n) ((T ^ (-n)) z) ∈ W := (hVO h).2.1
      rw [← homeoPow_add, add_neg_cancel, homeoPow_zero] at h1
      exact hz h1
    show (T ^ swapCocycle T V n z) z = z
    rw [swapCocycle_of_notMem_notMem T n hzV hzV', homeoPow_zero]
  · show (T ^ swapCocycle T V n x) x ≠ x
    rw [swapCocycle_of_mem T n hxV]
    exact hnx'

/-- Rigid stabilizers reflect inclusion of an open set in a closed set. -/
theorem subset_of_forall_supportedIn [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {U U' : Set X} (hU : IsOpen U)
    (hU' : IsClosed U')
    (h : ∀ g ∈ topologicalFullGroup T, SupportedIn g U → SupportedIn g U') : U ⊆ U' := by
  intro x hxU
  by_contra hxU'
  obtain ⟨g, hg, hgW, z, hz⟩ :=
    exists_supportedIn_ne_one hT (hU.inter hU'.isOpen_compl) ⟨x, hxU, hxU'⟩
  have h1 : SupportedIn g U' := h g hg (hgW.mono Set.inter_subset_left)
  by_cases hzU' : z ∈ U'
  · exact hz (hgW z fun hzW => hzW.2 hzU')
  · exact hz (h1 z hzU')

/-- Clopen sets with the same rigid stabilizer in `[[T]]` are equal. -/
theorem eq_of_forall_supportedIn_iff [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {U U' : Set X} (hU : IsClopen U)
    (hU' : IsClopen U')
    (h : ∀ g ∈ topologicalFullGroup T, SupportedIn g U ↔ SupportedIn g U') : U = U' :=
  Set.Subset.antisymm
    (subset_of_forall_supportedIn hT hU.isOpen hU'.isClosed fun g hg => (h g hg).1)
    (subset_of_forall_supportedIn hT hU'.isOpen hU.isClosed fun g hg => (h g hg).2)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_conj_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.continuous_swapCocycle
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.swapFun_involutive
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_supportedIn_ne_one
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.subset_of_forall_supportedIn
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.eq_of_forall_supportedIn_iff
