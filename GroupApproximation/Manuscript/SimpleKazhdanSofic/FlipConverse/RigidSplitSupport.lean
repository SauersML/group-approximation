import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidCentralizer
import GroupApproximation.Meta.AxiomGuard

/-!
# Rigid split, part 1: moved sets of elements of `[[T]]`

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").

* `movedSet g = {x | g x ≠ x}`; `SupportedIn g U ↔ movedSet g ⊆ U`.
* `isClopen_movedSet`: for aperiodic `T` and `g ∈ [[T]]` with `g x = T^{n(x)} x`, the moved set
  is `n⁻¹ (ℤ \ {0})`, a clopen set.
* `exists_supportedIn_apply_ne`: every point `x` of an open set `W` is moved by an involution of
  `[[T]]` supported in `W` (the swap of a small clopen `V ∋ x` with `T^n V`, as in
  `exists_supportedIn_ne_one`, whose construction moves the chosen point).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- The set of points moved by `g`. -/
def movedSet (g : X ≃ₜ X) : Set X := {x | g x ≠ x}

theorem supportedIn_iff_movedSet_subset {g : X ≃ₜ X} {U : Set X} :
    SupportedIn g U ↔ movedSet g ⊆ U := by
  constructor
  · intro hg x hx
    have hx' : g x ≠ x := hx
    by_contra hxU
    exact hx' (hg x hxU)
  · intro hsub x hxU
    by_contra hne
    exact hxU (hsub hne)

theorem isClopen_movedSet {T g : X ≃ₜ X} (hT : IsAperiodic T)
    (hg : g ∈ topologicalFullGroup T) : IsClopen (movedSet g) := by
  obtain ⟨n, hn, hgn⟩ := mem_topologicalFullGroup.1 hg
  have hset : movedSet g = n ⁻¹' ({0}ᶜ : Set ℤ) := by
    ext x
    constructor
    · intro hx h0
      have hx' : g x ≠ x := hx
      have h0' : n x = 0 := h0
      exact hx' (by rw [hgn x, h0', homeoPow_zero])
    · intro h0 hx
      have hx' : g x = x := hx
      have h1 : (T ^ n x) x = x := (hgn x).symm.trans hx'
      have h0' : n x ≠ 0 := h0
      exact h0' (hT x (n x) h1)
  rw [hset]
  exact (isClopen_discrete ({0}ᶜ : Set ℤ)).preimage hn

/-- Every point of an open set is moved by an element of `[[T]]` supported in that set. -/
theorem exists_supportedIn_apply_ne [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {W : Set X} (hW : IsOpen W) {x : X}
    (hxW : x ∈ W) :
    ∃ g ∈ topologicalFullGroup T, SupportedIn g W ∧ g x ≠ x := by
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
    fun z hz => ?_, ?_⟩
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

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.movedSet
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportedIn_iff_movedSet_subset
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isClopen_movedSet
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_supportedIn_apply_ne
