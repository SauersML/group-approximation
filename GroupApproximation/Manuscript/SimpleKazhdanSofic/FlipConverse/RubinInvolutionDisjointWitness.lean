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

/-- If `P * P = 1` and `h` commutes with `P h P`, then `h (P h P)` commutes with `P`. -/
theorem rubinInvDisj_conj_commute {G : Type*} [Group G] {P h : G} (hPP : P * P = 1)
    (hq : h * (P * h * P) = P * h * P * h) : h * (P * h * P) * P = P * (h * (P * h * P)) := by
  have hPP' : ∀ y, P * (P * y) = y := fun y => by rw [← mul_assoc, hPP, one_mul]
  conv_rhs => rw [hq]
  simp only [mul_assoc, hPP, hPP', mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_conj_commute

/-- Case `f x ≠ k x` for commuting involutions: the witness `h (P h P)` with `P = f k`. -/
theorem rubinInvDisj_caseMove [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {f k : X ≃ₜ X}
    (hf : f ∈ topologicalFullGroup T) (hk : k ∈ topologicalFullGroup T)
    (hff : ∀ z, f (f z) = z) (hkk : ∀ z, k (k z) = z) (hfk : f * k = k * f) {x : X}
    (hxf : x ∈ movedSet f) (hxk : x ∈ movedSet k) (hne : f x ≠ k x) :
    ∃ g ∈ topologicalFullGroup T, g * (f * k) = (f * k) * g ∧
      f * (g * f * g⁻¹) ≠ (g * f * g⁻¹) * f := by
  have hfx : f x ≠ x := hxf
  have hkx : k x ≠ x := hxk
  have hkf : ∀ w, k (f w) = f (k w) := fun w => (DFunLike.congr_fun hfk w).symm
  have hPx : f (k x) ≠ x := fun e => hne (calc
    f x = f (f (k x)) := by rw [e]
    _ = k x := hff _)
  have hPfx : f (k x) ≠ f x := fun e => hkx (f.injective e)
  obtain ⟨A1, B1, hA1, hB1, hxA1, hB1x, hAB1⟩ := t2_separation hfx.symm
  obtain ⟨A2, B2, hA2, hB2, hxA2, hB2x, hAB2⟩ := t2_separation hPx.symm
  obtain ⟨A3, B3, hA3, hB3, hA3x, hB3x, hAB3⟩ := t2_separation hPfx.symm
  obtain ⟨W, hWo, hxW, hW⟩ : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ w ∈ W,
      w ∈ A1 ∧ w ∈ A2 ∧ f w ∈ B1 ∧ f w ∈ A3 ∧ f (k w) ∈ B2 ∧ f (k w) ∈ B3 :=
    ⟨_, ((hA1.inter hA2).inter ((hB1.preimage f.continuous).inter
        (hA3.preimage f.continuous))).inter
        ((hB2.preimage (f * k).continuous).inter (hB3.preimage (f * k).continuous)),
      ⟨⟨⟨hxA1, hxA2⟩, hB1x, hA3x⟩, hB2x, hB3x⟩,
      fun w hw => ⟨hw.1.1.1, hw.1.1.2, hw.1.2.1, hw.1.2.2, hw.2.1, hw.2.2⟩⟩
  obtain ⟨h, hh, hhW, hhx⟩ := rubinInvDisj_exists_supportedIn_sq_ne hT hWo hxW
  have hfW : ∀ w ∈ W, f w ∉ W := fun w hw hv =>
    Set.disjoint_left.1 hAB1 (hW _ hv).1 (hW _ hw).2.2.1
  have hPw : ∀ w ∈ W, f (k w) ∉ W := fun w hw hv =>
    Set.disjoint_left.1 hAB2 (hW _ hv).2.1 (hW _ hw).2.2.2.2.1
  have hPfw : ∀ w ∈ W, f (k (f w)) ∉ W := fun w hw hv => by
    have h1 := (hW _ hv).2.2.2.1
    rw [hff, hkf] at h1
    exact Set.disjoint_left.1 hAB3 h1 (hW _ hw).2.2.2.2.2
  have hPPw : ∀ w, f (k (f (k w))) = w := fun w => by rw [hkf, hff, hkk]
  have hPP : f * k * (f * k) = 1 := Homeomorph.ext hPPw
  have hq : ∀ w ∈ W, (f * k * h * (f * k)) w = w ∧
      (f * k * h * (f * k)) (f w) = f w := fun w hw => by
    refine ⟨?_, ?_⟩
    · show f (k (h (f (k w)))) = w
      rw [hhW _ (hPw w hw), hPPw]
    · show f (k (h (f (k (f w))))) = f w
      rw [hhW _ (hPfw w hw), hPPw]
  have hqW : SupportedIn (f * k * h * (f * k)) Wᶜ := fun z hz =>
    (hq z (Set.notMem_compl_iff.1 hz)).1
  have hcomm : h * (f * k * h * (f * k)) = f * k * h * (f * k) * h :=
    SupportedIn.commute_of_compl hhW hqW
  have hP : f * k ∈ topologicalFullGroup T := Subgroup.mul_mem _ hf hk
  exact ⟨h * (f * k * h * (f * k)),
    Subgroup.mul_mem _ hh (Subgroup.mul_mem _ (Subgroup.mul_mem _ hP hh) hP),
    rubinInvDisj_conj_commute hPP hcomm,
    rubinInvDisj_not_commute_of_local hff hxW hhW hhx hfW hq⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_caseMove

/-- The converse direction: commuting involutions of `[[T]]` satisfying the centraliser
condition (with `g` ranging over `[[T]]`) have disjoint moved sets. -/
theorem rubinInvDisj_disjoint_of_formula [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {f k : X ≃ₜ X} (hf : f ∈ topologicalFullGroup T) (hk : k ∈ topologicalFullGroup T)
    (hff : f * f = 1) (hkk : k * k = 1) (hfk : f * k = k * f)
    (hform : ∀ g ∈ topologicalFullGroup T, g * (f * k) = (f * k) * g →
      f * (g * f * g⁻¹) = (g * f * g⁻¹) * f) :
    Disjoint (movedSet f) (movedSet k) := by
  have hff' : ∀ z, f (f z) = z := fun z => DFunLike.congr_fun hff z
  have hkk' : ∀ z, k (k z) = z := fun z => DFunLike.congr_fun hkk z
  refine Set.disjoint_left.2 fun x hxf hxk => ?_
  by_cases hne : f x = k x
  · obtain ⟨g, hg, hgc, hgn⟩ := rubinInvDisj_caseFix hT hf hk hff' hxf hne
    exact hgn (hform g hg hgc)
  · obtain ⟨g, hg, hgc, hgn⟩ := rubinInvDisj_caseMove hT hf hk hff' hkk' hfk hxf hxk hne
    exact hgn (hform g hg hgc)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinInvDisj_disjoint_of_formula

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
