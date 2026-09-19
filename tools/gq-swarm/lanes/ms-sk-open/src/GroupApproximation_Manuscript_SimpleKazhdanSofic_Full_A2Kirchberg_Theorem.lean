import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.KazhdanFixedSpace
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.ResiduallyFinite
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.NearInvariant
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Kirchberg.TraceModels
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Kirchberg.Frame

/-!
# Kirchberg's theorem (lane A2Kirchberg)

`simple_kazhdan_sofic_group.tex`, Introduction, table row A2 (tex l.54--59; bibitem l.864--866):
Kirchberg, *Discrete groups with Kazhdan's property T and factorization property are residually
finite*, Math. Ann. **299** (1994), Theorem 1.1.

**A group with property (T) and the factorization property is residually finite.**

Proof.  `G` is finitely generated (property (T)).  Fix `h ≠ 1`.  Take a Kazhdan pair `(Q, ε)` and
a matrix model `X = Xₙ` of the canonical trace at an index where the Gram estimates at `Q` hold
to within `ε²/32` and `|Re tr X(h)| / k < 1/4`.  The frame vector `η` of the real dilation
`σ` of `X` is moved by less than `ε/4` by `σ ⊗ σ` at `Q`, so it is `1/4`-close to an invariant
vector `ζ` of `K ⊗̂ K`.  If `σ(h)` fixed every vector of every finite-dimensional invariant
subspace, the compact slices of `ζ` would see no `σ(h)` on the first leg, so
`⟪ζ, η⟫ = ⟪ζ, η_h⟫` with `η_h = (2k)^{-1/2} ∑ₐ σ(h) f_a ⊗ f_a`.  But `⟪ζ, η⟫ > 3/4` while
`⟪ζ, η_h⟫ < 1/4 + 1/4`, as `⟪η, η_h⟫ = Re tr X(h) / k`.  So `h` acts nontrivially in a
finite-dimensional orthogonal representation, and residual finiteness follows.
-/

namespace GroupApproximation.Full.A2Kirchberg

universe u

/-- The real part of the normalized trace. -/
theorem re_normTrace (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    (normTrace Y A).re = (Matrix.trace A).re / (Fintype.card Y : ℝ) := by
  rw [normTrace, ← Complex.ofReal_natCast, Complex.div_ofReal_re]

/-- **The dilation-and-tensor-square step of Kirchberg's Theorem 1.1** (tex l.54--59).
For a positive definite `X` with `X(1) = 1`, good Gram estimates at a Kazhdan set and small trace
at `h`, the element `h` moves a vector of a finite-dimensional invariant subspace of the real
dilation. -/
theorem exists_moving_of_generic {G : Type u} [Group G] {Y : Type} [Fintype Y] [DecidableEq Y]
    (X : G → Matrix Y Y ℂ) (hX : RealDilation.IsPositiveDefinite X) (hone : X 1 = 1)
    (hk : 0 < Fintype.card Y) {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (hgram : ∀ q ∈ Q,
      1 - ε ^ 2 / 32 < (∑ x : Y, ∑ y : Y, ‖X q x y‖ ^ 2) / (Fintype.card Y : ℝ))
    {h : G} (htr : (Matrix.trace (X h)).re / (Fintype.card Y : ℝ) < 1 / 4) :
    ∃ W : Submodule ℝ (RealDilation.Space X hX), FiniteDimensional ℝ W ∧
      CompactExtraction.IsInvariant (RealDilation.rep X hX) W ∧
      ∃ v ∈ W, RealDilation.rep X hX h v ≠ v := by
  have hc : 0 < ε * (1 / 4) := mul_pos hQ.1 (by norm_num)
  have hmove : ∀ q ∈ Q, ‖TensorSq.diag (RealDilation.rep X hX) q (Frame.kEta X hX)
      - Frame.kEta X hX‖ < ε * (1 / 4) := by
    intro q hq
    refine Frame.norm_diag_kEta_sub_lt X hX hone hk hc q ?_
    have h32 : (ε * (1 / 4)) ^ 2 / 2 = ε ^ 2 / 32 := by ring
    rw [h32]
    exact hgram q hq
  obtain ⟨ζ, hζ, hnear⟩ := A2LocalLifting.exists_invariant_near hQ
    (TensorSq.diag (RealDilation.rep X hX)) (Frame.kEta X hX) (by norm_num : (0 : ℝ) < 1 / 4)
    hmove
  by_contra hne
  have hfd : ∀ W : Submodule ℝ (RealDilation.Space X hX), FiniteDimensional ℝ W →
      CompactExtraction.IsInvariant (RealDilation.rep X hX) W →
      ∀ v ∈ W, RealDilation.rep X hX h v = v := by
    intro W hW hinv v hv
    by_contra hmov
    exact hne ⟨W, hW, hinv, v, hv, hmov⟩
  have hid : ∀ x y : RealDilation.Space X hX,
      inner ℝ ζ (TensorSq.tmulC (RealDilation.rep X hX h x) y)
        = inner ℝ ζ (TensorSq.tmulC x y) :=
    TensorSq.inner_tmulC_of_forall_fixed (RealDilation.rep X hX) ζ hζ h hfd
  have heq := Frame.inner_kEtaMoved_eq X hX (RealDilation.rep X hX h) ζ hid
  have h1 := Frame.inner_gt_of_near (Frame.norm_kEta X hX hone hk) hnear
  have h2 := Frame.inner_lt_of_near
    (Frame.norm_kEtaMoved X hX hone hk (RealDilation.rep X hX h)) hnear
    (by rw [Frame.inner_kEta_kEtaMoved_rep X hX hone h]; exact htr)
  rw [heq] at h2
  linarith

/-- **Every nontrivial element acts nontrivially in a finite-dimensional orthogonal
representation**, for a group with property (T) and the factorization property (Kirchberg,
Math. Ann. 299 (1994), proof of Theorem 1.1; tex l.54--59). -/
theorem exists_moving_representation {G : Type u} [Group G]
    (hT : HasKazhdanPropertyT.{u, u} G) (hF : NinetyNineProblems.HasFactorizationProperty G)
    (h : G) (hh : h ≠ 1) :
    ∃ (W : Type u) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W)
      (_ : FiniteDimensional ℝ W) (ρ : G →* (W ≃ₗᵢ[ℝ] W)), ρ h ≠ 1 := by
  obtain ⟨Q, ε, hQ⟩ := hT
  have hF' : Nonempty (Quasidiagonal.AmenableTraceModel
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) := hF
  obtain ⟨M⟩ := hF'
  have hδ : (0 : ℝ) < min (ε ^ 2 / 32) (1 / 4) :=
    lt_min (div_pos (pow_pos hQ.1 2) (by norm_num)) (by norm_num)
  obtain ⟨n, hk, hgram, htr⟩ := TraceModels.exists_index M Q hh hδ
  have hX : RealDilation.IsPositiveDefinite (AmenableTraceHyperlinear.modelMatrix M n) :=
    ⟨fun g ↦ AmenableTraceHyperlinear.modelMatrix_conjTranspose M n g,
      fun m g w ↦ TraceModels.modelMatrix_kernel_nonneg M n m g w⟩
  have hgram' : ∀ q ∈ Q, 1 - ε ^ 2 / 32 <
      (∑ x : M.space n, ∑ y : M.space n, ‖AmenableTraceHyperlinear.modelMatrix M n q x y‖ ^ 2)
        / (Fintype.card (M.space n) : ℝ) := by
    intro q hq
    have h1 := (abs_lt.mp (hgram q hq)).1
    rw [re_normTrace, RealForms.re_trace_conjTranspose_mul] at h1
    have h2 := min_le_left (ε ^ 2 / 32) (1 / 4)
    linarith
  have htr' : (Matrix.trace (AmenableTraceHyperlinear.modelMatrix M n h)).re
      / (Fintype.card (M.space n) : ℝ) < 1 / 4 := by
    have h1 := (abs_lt.mp htr).2
    rw [re_normTrace] at h1
    have h2 := min_le_right (ε ^ 2 / 32) (1 / 4)
    linarith
  obtain ⟨W, hWfd, hWinv, v, hvW, hv⟩ :=
    exists_moving_of_generic (AmenableTraceHyperlinear.modelMatrix M n) hX
      (TraceModels.modelMatrix_one M n) hk hQ hgram' htr'
  refine ⟨↥W, inferInstance, inferInstance, hWfd,
    KazhdanFixedSpace.restrictToInvariantSubspace (RealDilation.rep _ hX) W hWinv, ?_⟩
  intro h1
  apply hv
  exact congrArg (fun e : W ≃ₗᵢ[ℝ] W ↦ ((e ⟨v, hvW⟩ : W) : RealDilation.Space _ hX)) h1

/-- **Kirchberg's theorem** (Kirchberg, Math. Ann. 299 (1994), Theorem 1.1; table row A2 of
`simple_kazhdan_sofic_group.tex`, tex l.54--59): a group with property (T) and the factorization
property is residually finite. -/
theorem isResiduallyFinite_of_hasKazhdanPropertyT_of_hasFactorizationProperty
    {G : Type u} [Group G] (hT : HasKazhdanPropertyT.{u, u} G)
    (hF : NinetyNineProblems.HasFactorizationProperty G) :
    IsResiduallyFinite G := by
  haveI : Group.FG G := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT G hT
  exact A2LocalLifting.isResiduallyFinite_of_forall_ne_one
    (fun x hx ↦ exists_moving_representation hT hF x hx)

/-- **An infinite simple Kazhdan group does not have the factorization property** (tex l.54--59,
table row A2: the Kirchberg step of Ozawa's no-LLP remark). -/
theorem not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan
    (G : Type u) [Group G] [IsSimpleGroup G] [Infinite G]
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ¬ NinetyNineProblems.HasFactorizationProperty G := fun hF ↦
  NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite G
    (isResiduallyFinite_of_hasKazhdanPropertyT_of_hasFactorizationProperty hT hF)

end GroupApproximation.Full.A2Kirchberg
