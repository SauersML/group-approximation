import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SpatialInvolutions
import GroupApproximation.Meta.AxiomGuard

/-!
# Involutive elements of `[[T]]` with small support

Census row `2e7c7d9ab149` ("for topological full groups the converse holds"). The row is absent
from the current tex, so there is no tex line to quote. This file is infrastructure for the
Matui/Bezuglyi–Medynets route to `SupportDisjointnessTransportStatement` (lanes sk-flip-08 → 09 → 10).

The corpus lemmas `exists_supportedIn_ne_one` (SpatialInvolutions.lean) and
`exists_supportedIn_apply_ne` (RigidSplitSupport.lean) build their witness as the swap
involution `swapFun T V n`, but their statements do not record `g * g = 1`. Since that
information cannot be recovered from the statements, we re-run the construction here and
keep the involution law.

Let `T` be a minimal homeomorphism of a compact Hausdorff, totally disconnected, perfect space,
let `W` be open and `x ∈ W`.

* Perfectness gives `y ∈ W \ {x}`, and minimality gives `n` with `T^n x ∈ W \ {x}`.
* Separate `x` from `T^n x` by open sets `A ∋ x` and `B ∋ T^n x`. A clopen `V ∋ x` inside
  `W ∩ A ∩ T^{-n}(W ∩ B)` satisfies `V ∩ T^n V = ∅` and `V ∪ T^n V ⊆ W`.
* `σ := swapFun T V n` is `T^n` on `V`, `T^{-n}` on `T^n V`, and the identity elsewhere. It lies
  in `[[T]]` via the continuous cocycle `swapCocycle T V n` and is supported in `W`.
* `σ x = T^n x ≠ x`, and `σ ∘ σ = id` by `swapFun_involutive`, i.e. `σ * σ = 1`.

Endpoints: `exists_involution_supportedIn_apply_ne`, `exists_involution_supportedIn_ne_one`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- Every point of an open set is moved by an involution of `[[T]]` supported in that set. -/
theorem exists_involution_supportedIn_apply_ne [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {W : Set X} (hW : IsOpen W) {x : X} (hxW : x ∈ W) :
    ∃ g ∈ topologicalFullGroup T, g * g = 1 ∧ SupportedIn g W ∧ g x ≠ x := by
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
    Homeomorph.ext fun z => ?_, fun z hz => ?_, ?_⟩
  · show swapFun T V n (swapFun T V n z) = z
    exact hinv z
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

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_involution_supportedIn_apply_ne

/-- Every nonempty open set supports a nontrivial involution of `[[T]]`. -/
theorem exists_involution_supportedIn_ne_one [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ g ∈ topologicalFullGroup T, g * g = 1 ∧ SupportedIn g W ∧ ∃ x, g x ≠ x := by
  obtain ⟨x, hxW⟩ := hne
  obtain ⟨g, hg, hgg, hgW, hgx⟩ := exists_involution_supportedIn_apply_ne hT hW hxW
  exact ⟨g, hg, hgg, hgW, x, hgx⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.exists_involution_supportedIn_ne_one

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
