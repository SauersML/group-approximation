import GroupApproximation.Analysis.VoiculescuBlockRecursion

/-!
# (V4) Block-diagonal absorption, proved from the intertwining step

This closes the block-diagonal case of the assembly.  The intertwining step is
run once per block, the recursion of `Analysis/VoiculescuBlockRecursion` keeps
the ranges orthogonal, `Analysis/VoiculescuBlockIsometry` sums the pieces into a
single isometry, and `Analysis/VoiculescuBlockCompact` turns the summable block
defects into compactness.

## Two hypotheses the construction cannot do without

`Analysis/VoiculescuBlockDiagonal` used to carry an absorption statement without
them; it was retired in the commit that landed this module, because it asked for
its conclusion under hypotheses that cannot supply it.  The two are:

* **Separability of `↥A`.**  The recursion constrains the defect against a finite
  set at each stage, so only countably many elements of `A` are ever named; the
  conclusion is claimed for *every* `a`, and the passage from the countable set
  to all of `A` is density.  Voiculescu's theorem genuinely needs the algebra
  separable, so this is not an artefact of the route.
* **Contractivity of `ρ`.**  The same passage needs `a ↦ σ(a)W - Wρ(a)` to be
  continuous.  A `⋆`-homomorphism of C⋆-algebras is automatically contractive,
  but `↥A` carries no registered `CStarAlgebra` instance, so the fact is not
  available and is asked for instead.

Both are stated explicitly rather than smuggled in, and the statement proved here
is named for the difference.  Whether the unhypothesised form is outright false
was not settled; what is settled is that it does not follow by this route, which
is why it was removed rather than recorded as a refutation.

## Where each earlier module is spent

The recursion supplies orthogonal ranges; the blocks' finite-dimensionality is
what makes each stage's obstruction admissible.  The tolerance is `2⁻ᵐ`, which is
`ℓ¹`, which is what makes the compactness argument a norm limit of finite-rank
operators rather than a tail estimate.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

/-! ## Two estimates, taken abstractly

Both are about a bare pair of operators, with no subalgebra in sight.  Proved in
place they do not elaborate: every `‖(c : H →L[ℂ] H)‖` drags `↥A`'s norm instance
through the unifier and the defect bound times out at `isDefEq`.  Stated over
plain continuous linear maps they are immediate.  Same lesson as the `PiLp`
traps: prove at the abstract operator level, then transport. -/

variable {K H : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace K] [CompleteSpace H] in
/-- The defect is linear in the pair. -/
theorem defect_sub (Wc : K →L[ℂ] H) (S S' : H →L[ℂ] H) (R R' : K →L[ℂ] K) :
    (S ∘L Wc - Wc ∘L R) - (S' ∘L Wc - Wc ∘L R')
      = (S - S') ∘L Wc - Wc ∘L (R - R') := by
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  abel

omit [CompleteSpace K] [CompleteSpace H] in
/-- The defect of a contraction is bounded by twice the operator's norm. -/
theorem norm_defect_le (Wc : K →L[ℂ] H) (hWc : ‖Wc‖ ≤ 1) (S : H →L[ℂ] H)
    (R : K →L[ℂ] K) (hR : ‖R‖ ≤ ‖S‖) : ‖S ∘L Wc - Wc ∘L R‖ ≤ 2 * ‖S‖ := by
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖S ∘L Wc‖ ≤ ‖S‖ := by
    refine le_trans (S.opNorm_comp_le Wc) ?_
    calc ‖S‖ * ‖Wc‖ ≤ ‖S‖ * 1 := mul_le_mul_of_nonneg_left hWc (norm_nonneg _)
      _ = ‖S‖ := mul_one _
  have h2 : ‖Wc ∘L R‖ ≤ ‖S‖ := by
    refine le_trans (Wc.opNorm_comp_le R) ?_
    calc ‖Wc‖ * ‖R‖ ≤ 1 * ‖S‖ := mul_le_mul hWc hR (norm_nonneg _) zero_le_one
      _ = ‖S‖ := one_mul _
  linarith

omit [CompleteSpace K] in
/-- Compactness extends from a dense sequence when the defect is additive and
uniformly norm-controlled.  Keeping this closure argument separate gives its
elaboration an independent heartbeat budget. -/
theorem isCompactOperator_of_dense_defect
    {E : Type} [NormedAddCommGroup E] (d : ℕ → E) (hd : DenseRange d)
    (D : E → (K →L[ℂ] H))
    (hcompact : ∀ k, IsCompactOperator (D (d k)))
    (hsub : ∀ a b, D a - D b = D (a - b))
    (hbound : ∀ c, ‖D c‖ ≤ 2 * ‖c‖) :
    ∀ a, IsCompactOperator (D a) := by
  intro a
  have hmem : D a ∈ closure {T : K →L[ℂ] H | IsCompactOperator T} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hd a (ε / 3) (by positivity)
    refine ⟨D (d k), hcompact k, ?_⟩
    rw [dist_eq_norm, hsub a (d k)]
    have hlt : ‖a - d k‖ < ε / 3 := by
      simpa only [dist_eq_norm] using hk
    have hb := hbound (a - d k)
    nlinarith
  rwa [isClosed_setOf_isCompactOperator.closure_eq] at hmem

/-- **(V4) over block-diagonal representations, with the hypotheses the
construction consumes**: a representation decomposing into finite-dimensional
invariant blocks is contained, modulo the compacts, in any essential subalgebra
of `B(H)`, given `↥A` separable and `ρ` contractive. -/
def SeparableBlockDiagonalAbsorptionStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)), IsClosed (A : Set (H →L[ℂ] H)) →
      (∀ T ∈ A, IsCompactOperator T → T = 0) →
      TopologicalSpace.SeparableSpace ↥A →
      ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] (rho : ↥A →⋆ₐ[ℂ] (K →L[ℂ] K)),
        (∀ a : ↥A, ‖rho a‖ ≤ ‖(a : H →L[ℂ] H)‖) → InvariantBlocks rho →
          ∃ W : K →L[ℂ] H, ContinuousLinearMap.adjoint W ∘L W = 1 ∧
            ∀ a : ↥A, IsCompactOperator ((a : H →L[ℂ] H) ∘L W - W ∘L rho a)

/-- **The block-diagonal case of (V4), proved.** -/
theorem separableBlockDiagonalAbsorption_of_intertwiningStep
    (hIS : IntertwiningStepStatement) :
    SeparableBlockDiagonalAbsorptionStatement := by
  classical
  intro H _ _ _ A hAclosed hAK hsepA K _ _ _ rho hrho B
  haveI := hsepA
  haveI : ∀ m, FiniteDimensional ℂ ↥(B.sub m) := B.finiteDimensional
  haveI : Nonempty ↥A := ⟨0⟩
  set d : ℕ → ↥A := TopologicalSpace.denseSeq ↥A with hddef
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq ↥A
  set eps : ℕ → ℝ := fun m ↦ (1 / 2 : ℝ) ^ m with hepsdef
  have hepspos : ∀ m, 0 < eps m := fun m ↦ by positivity
  set F : ℕ → Finset ↥A := fun m ↦ (Finset.range (m + 1)).image d with hFdef
  -- one stage of the construction
  have step : ∀ (m : ℕ) (P : Submodule ℂ H), FiniteDimensional ℂ ↥P →
      ∃ V : ↥(B.sub m) →L[ℂ] H,
        ContinuousLinearMap.adjoint V ∘L V = 1 ∧ (∀ x, V x ∈ Pᗮ) ∧
        ∀ a ∈ F m, ‖(a : H →L[ℂ] H) ∘L V - V ∘L (B.rep m) a‖ < eps m := by
    intro m P hP
    exact hIS H A hAclosed hAK ↥(B.sub m) (B.rep m) (F m) (eps m) (hepspos m) P hP
  obtain ⟨V, hViso, hVQ, hVorth⟩ :=
    exists_seq_orthogonal_ranges (G := fun m ↦ ↥(B.sub m)) _ step
  -- the stages as linear isometries
  have hVnorm : ∀ (m : ℕ) (x : ↥(B.sub m)), ‖V m x‖ = ‖x‖ := by
    intro m x
    have hiso := (ContinuousLinearMap.isometry_iff_adjoint_comp_self (V m)).mpr
      (hViso m)
    exact hiso.norm_map_of_map_zero (map_zero _) x
  set Vli : ∀ m, ↥(B.sub m) →ₗᵢ[ℂ] H := fun m ↦ ⟨(V m).toLinearMap, hVnorm m⟩
    with hVlidef
  have hOF : OrthogonalFamily ℂ (fun m ↦ ↥(B.sub m)) Vli := by
    intro m n hmn x y
    exact hVorth m n hmn x y
  obtain ⟨W, hW⟩ := exists_linearIsometry_of_blocks
    (fun m ↦ (B.sub m).subtypeₗᵢ) B.isHilbertSum Vli hOF
  refine ⟨W.toContinuousLinearMap, ?_, ?_⟩
  · exact (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp W.isometry
  -- the defect
  set Wc : K →L[ℂ] H := W.toContinuousLinearMap with hWcdef
  have hWcnorm : ‖Wc‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
      rw [one_mul]
      exact le_of_eq (W.norm_map x)
  set Dm : ↥A → (K →L[ℂ] H) := fun a ↦ (a : H →L[ℂ] H) ∘L Wc - Wc ∘L rho a
    with hDmdef
  -- the defect restricted to a block is the stage's defect
  have hblock : ∀ (a : ↥A) (m : ℕ),
      Dm a ∘L sumBlockIncl (fun m ↦ (B.sub m).subtypeₗᵢ) m
        = (a : H →L[ℂ] H) ∘L V m - V m ∘L (B.rep m) a := by
    intro a m
    refine ContinuousLinearMap.ext fun x ↦ ?_
    have h1 : Wc ((B.sub m).subtypeₗᵢ x) = V m x := hW m x
    have h2 : Wc ((B.sub m).subtypeₗᵢ ((B.rep m) a x)) = V m ((B.rep m) a x) :=
      hW m ((B.rep m) a x)
    show (a : H →L[ℂ] H) (Wc ((x : K))) - Wc (rho a ((x : K)))
      = (a : H →L[ℂ] H) (V m x) - V m ((B.rep m) a x)
    rw [show ((x : K)) = (B.sub m).subtypeₗᵢ x from rfl, h1,
      show rho a ((B.sub m).subtypeₗᵢ x)
        = (B.sub m).subtypeₗᵢ ((B.rep m) a x) from rfl, h2]
  -- the defect is compact along the dense sequence
  have hcompact_d : ∀ k, IsCompactOperator (Dm (d k)) := by
    intro k
    refine isCompactOperator_of_summable_blocks
      (fun m ↦ (B.sub m).subtypeₗᵢ) B.isHilbertSum (Dm (d k)) ?_
    rw [← summable_nat_add_iff k]
    refine Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
      ((summable_geometric_two).mul_left ((1 / 2 : ℝ) ^ k))
    have hmem : d k ∈ F (m + k) := by
      refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
      exact Finset.mem_range.mpr (by omega)
    have hb := hVQ (m + k) (d k) hmem
    rw [← hblock (d k) (m + k)] at hb
    refine le_trans hb.le (le_of_eq ?_)
    rw [hepsdef]
    ring
  -- the defect is continuous in `a`
  have hDlin : ∀ a b : ↥A, Dm a - Dm b = Dm (a - b) := by
    intro a b
    have hcoe : ((a - b : ↥A) : H →L[ℂ] H)
        = (a : H →L[ℂ] H) - (b : H →L[ℂ] H) := rfl
    show ((a : H →L[ℂ] H) ∘L Wc - Wc ∘L rho a)
        - ((b : H →L[ℂ] H) ∘L Wc - Wc ∘L rho b)
      = ((a - b : ↥A) : H →L[ℂ] H) ∘L Wc - Wc ∘L rho (a - b)
    rw [hcoe, map_sub]
    exact defect_sub Wc _ _ _ _
  have hDbound : ∀ c : ↥A, ‖Dm c‖ ≤ 2 * ‖c‖ := fun c ↦
    norm_defect_le Wc hWcnorm _ _ (hrho c)
  exact isCompactOperator_of_dense_defect d hd Dm hcompact_d hDlin hDbound

/-- **The conclusion embeds the source isometrically.**  Carried over from the
retired statement, since the check is about the conclusion and not about the
hypotheses: it is what keeps the statement from asserting something about a
source too large to fit in `H`. -/
theorem isometry_of_separableBlockDiagonal
    (h : SeparableBlockDiagonalAbsorptionStatement)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAclosed : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0)
    (hsepA : TopologicalSpace.SeparableSpace ↥A)
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (rho : ↥A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hrho : ∀ a : ↥A, ‖rho a‖ ≤ ‖(a : H →L[ℂ] H)‖) (B : InvariantBlocks rho) :
    ∃ W : K →L[ℂ] H, Isometry W := by
  obtain ⟨W, hWiso, -⟩ := h H A hAclosed hAK hsepA K rho hrho B
  exact ⟨W, (ContinuousLinearMap.isometry_iff_adjoint_comp_self W).mpr hWiso⟩

/-- **The block-diagonal case of (V4), closed against Glimm's lemma.**  The whole
chain: Glimm, the amplification, the one-step approximation, the intertwining
exchange, the recursion, the block sum, and the summation analysis. -/
theorem separableBlockDiagonalAbsorption_of_glimm (hG : GlimmLemmaStatement) :
    SeparableBlockDiagonalAbsorptionStatement :=
  separableBlockDiagonalAbsorption_of_intertwiningStep (intertwiningStep_of_glimm hG)

end

end ShulmanFill
end GroupApproximation
