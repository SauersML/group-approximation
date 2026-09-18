import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinInvolutionDisjointBasic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolSmall
import GroupApproximation.Meta.AxiomGuard

/-!
# Group-theoretic definability of disjoint involution supports, part 2: witnesses

Lane `sk-flip-23c`.  Census row `2e7c7d9ab149` (no tex line).

`T` is minimal on a compact Hausdorff, totally disconnected, perfect space.  Let `f, k ∈ [[T]]`
be commuting involutions, put `P = f k`, and suppose `x` is moved by both `f` and `k`.  We build
`g ∈ [[T]]` in the centraliser of `P` with `[f, g f g⁻¹] ≠ 1`
(`rubinInvDisj_disjoint_of_formula`).
* Case `f x = k x` (`rubinInvDisj_caseFix`).  Then `P x = x`.  The moved set of `P` is clopen,
  so `x` has a neighbourhood `W` off it, with `W ∩ f W = ∅`.  Take `g = h` supported in `W`
  with `h (h x) ≠ x`.
* Case `f x ≠ k x` (`rubinInvDisj_caseMove`).  The points `x`, `f x` and `P x` are distinct.
  Choose `W ∋ x` with `W`, `f W`, `P W` and `P f W` pairwise disjoint.  Take `g = h q` with
  `q = P h P`.
In both cases `rubinInvDisj_not_commute_of_local` gives `[f, g f g⁻¹] ≠ 1`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

variable {X : Type*} [TopologicalSpace X]

/-- An element of `[[T]]` supported in `W` with `h (h x) ≠ x`: the product of two involutions. -/
theorem rubinInvDisj_exists_supportedIn_sq_ne [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {W : Set X} (hW : IsOpen W) {x : X} (hxW : x ∈ W) :
    ∃ h ∈ topologicalFullGroup T, SupportedIn h W ∧ h (h x) ≠ x := by
  obtain ⟨σ, hσ, hσσ, hσW, hσx⟩ := exists_involution_supportedIn_apply_ne hT hW hxW
  obtain ⟨A, B, hA, hB, hxA, hσxB, hAB⟩ := t2_separation hσx.symm
  have hxW' : x ∈ W ∩ A ∩ σ ⁻¹' B := ⟨⟨hxW, hxA⟩, hσxB⟩
  obtain ⟨τ, hτ, -, hτW, hτx⟩ := exists_involution_supportedIn_apply_ne hT
    ((hW.inter hA).inter (hB.preimage σ.continuous)) hxW'
  have hy : τ x ∈ W ∩ A ∩ σ ⁻¹' B := SupportedIn.apply_mem hτW hxW'
  have hσy : σ (τ x) ∉ W ∩ A ∩ σ ⁻¹' B := fun hv => Set.disjoint_left.1 hAB hv.1.2 hy.2
  have hτσy : τ (σ (τ x)) = σ (τ x) := hτW _ hσy
  have hσσ' : ∀ z, σ (σ z) = z := fun z => DFunLike.congr_fun hσσ z
  refine ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, fun z hz => ?_, ?_⟩
  · show σ (τ z) = z
    rw [hτW z (fun hz' => hz hz'.1.1), hσW z hz]
  · show σ (τ (σ (τ x))) ≠ x
    rw [hτσy, hσσ']
    exact hτx

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_exists_supportedIn_sq_ne

/-- Case `f x = k x`: a witness supported off the moved set of `f * k`. -/
theorem rubinInvDisj_caseFix [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {f k : X ≃ₜ X}
    (hf : f ∈ topologicalFullGroup T) (hk : k ∈ topologicalFullGroup T)
    (hff : ∀ z, f (f z) = z) {x : X} (hxf : x ∈ movedSet f) (hfx : f x = k x) :
    ∃ g ∈ topologicalFullGroup T, g * (f * k) = (f * k) * g ∧
      f * (g * f * g⁻¹) ≠ (g * f * g⁻¹) * f := by
  haveI : Nonempty X := ⟨x⟩
  haveI : Infinite X := infinite_of_perfectSpace
  have hPc : IsClopen (movedSet (f * k)) :=
    isClopen_movedSet (isAperiodic_of_isMinimalHomeo hT) (Subgroup.mul_mem _ hf hk)
  have hPx : x ∉ movedSet (f * k) := fun hv =>
    (hv : (f * k) x ≠ x) (show f (k x) = x by rw [← hfx, hff])
  have hfx' : f x ≠ x := hxf
  obtain ⟨A, B, hA, hB, hxA, hfxB, hAB⟩ := t2_separation hfx'.symm
  have hxW : x ∈ (movedSet (f * k))ᶜ ∩ A ∩ f ⁻¹' B := ⟨⟨hPx, hxA⟩, hfxB⟩
  obtain ⟨h, hh, hhW, hhx⟩ := rubinInvDisj_exists_supportedIn_sq_ne hT
    ((hPc.compl.isOpen.inter hA).inter (hB.preimage f.continuous)) hxW
  have hhO : SupportedIn h (movedSet (f * k))ᶜ := hhW.mono fun _ hw => hw.1.1
  have hPs : SupportedIn (f * k) (movedSet (f * k)) :=
    supportedIn_iff_movedSet_subset.2 fun _ hy => hy
  refine ⟨h * 1, Subgroup.mul_mem _ hh (Subgroup.one_mem _), ?_,
    rubinInvDisj_not_commute_of_local hff hxW hhW hhx ?_ ?_⟩
  · rw [mul_one]
    exact (SupportedIn.commute_of_compl hPs hhO).symm
  · intro w hw hfw
    exact Set.disjoint_left.1 hAB hfw.1.2 hw.2
  · intro w _
    exact ⟨rfl, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_caseFix
