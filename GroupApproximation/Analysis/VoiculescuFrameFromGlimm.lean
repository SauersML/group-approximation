import GroupApproximation.Analysis.VoiculescuAmplifiedUnits

/-!
# (V3) The frame, extracted from Glimm's lemma

This closes the one-step approximation against Glimm's lemma.  Everything the
extraction needs is already built: the amplification `Mₙ(A) ⊆ B(Hⁿ)` with its
compact intersection, the amplified representation, the state at the diagonal
vector, the matrix units, the obstruction subspace of `Hⁿ`, and the passage from
entries to operator norms.  What is left is to run Glimm's lemma on that data and
read the answer.

## What the reading is

Glimm's lemma returns a unit vector `η` of `Hⁿ`, orthogonal to the obstruction,
with `⟪η, u η⟫` close to `ψ(u)` for each matrix unit `u = ι_k a π_l`.  The two
sides of that are `⟪η_k, a η_l⟫` and `n⁻¹⟪e_k, ρ(a) e_l⟫`, so the rescaled tuple
`ξ_i = √n · η_i` has `⟪ξ_k, a ξ_l⟫` within `n·ε'` of `⟪e_k, ρ(a) e_l⟫`.  Taking
`a = 1` says the `ξ_i` are almost orthonormal, which is the Gram clause; taking
`a` in the given finite set gives the compression clause.  The frame is then
`frameOfTuple`, and the operator bounds come from `frame_bounds_of_entries` with
the loss `n²` of that estimate, so running Glimm at `ε' = ε/(2(n³+1))` finishes.

## The degenerate case

At a zero representation space every operator on `K₀` is every other, so `T = 0`
satisfies all three clauses and no state has to be built.  That is the case the
state's `n ≠ 0` hypothesis excludes, and it is handled first.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace ComplexOrder

noncomputable section

/-- **(V3a) discharged.**  Glimm's lemma, run on the amplification at the state
of the diagonal vector, produces the frame. -/
theorem frameApproximation_of_glimm (hG : GlimmLemmaStatement) :
    FrameApproximationStatement := by
  classical
  intro H _ _ _ A hAclosed hAK K₀ _ _ _ _ rho F eps heps V hV
  by_cases hK0 : ∀ x : K₀, x = 0
  · -- The representation space is zero: every operator on it is every other.
    have htriv : ∀ S T : K₀ →L[ℂ] K₀, S = T := by
      intro S T
      refine ContinuousLinearMap.ext fun x ↦ ?_
      rw [hK0 x, map_zero, map_zero]
    refine ⟨0, fun x ↦ ?_, ?_, ?_⟩
    · simp
    · rw [htriv (ContinuousLinearMap.adjoint (0 : K₀ →L[ℂ] H) ∘L 0) 1, sub_self,
        norm_zero]
      exact heps
    · intro a _
      rw [htriv (ContinuousLinearMap.adjoint (0 : K₀ →L[ℂ] H) ∘L (a : H →L[ℂ] H) ∘L 0)
        (rho a), sub_self, norm_zero]
      exact heps
  · haveI : FiniteDimensional ℂ ↥V := hV
    have hn : Module.finrank ℂ K₀ ≠ 0 := fun h ↦
      hK0 (_root_.finrank_zero_iff_forall_zero.mp h)
    set n := Module.finrank ℂ K₀ with hndef
    set b := stdOrthonormalBasis ℂ K₀ with hbdef
    have hN0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    -- the tolerance Glimm is run at
    have hden : (0:ℝ) < 2 * ((n:ℝ)^3 + 1) := by positivity
    set eps' : ℝ := eps / (2 * ((n:ℝ)^3 + 1)) with heps'def
    have heps'0 : 0 < eps' := div_pos heps hden
    have hmul : eps' * (2 * ((n:ℝ)^3 + 1)) = eps := by
      rw [heps'def]; field_simp
    -- the finite set of matrix units
    set G : Finset ↥(ampSubalgebra A n) :=
      Finset.image (fun t : ↥A × Fin n × Fin n ↦ matrixUnit A t.1 t.2.1 t.2.2)
        ((insert (1 : ↥A) F) ×ˢ (Finset.univ ×ˢ Finset.univ)) with hGdef
    have hGmem : ∀ a ∈ insert (1 : ↥A) F, ∀ k l : Fin n,
        matrixUnit A a k l ∈ G := by
      intro a ha k l
      refine Finset.mem_image.mpr ⟨(a, k, l), ?_, rfl⟩
      simp [Finset.mem_product, ha]
    -- run Glimm's lemma
    obtain ⟨eta, -, hetaperp, hetaapprox⟩ :=
      hG (BlockSpace H n) (ampSubalgebra A n)
        (isClosed_ampSubalgebra A n hAclosed)
        (ampSubalgebra_compactMem_eq_zero A n hAK)
        (ampState A hAclosed n b rho) (ampState_one hAclosed hn b rho)
        G eps' heps'0 (blockObstruction n V) (finiteDimensional_blockObstruction V)
    -- the rescaled tuple
    set xi : Fin n → H :=
      fun i ↦ ((Real.sqrt (n : ℝ) : ℝ) : ℂ) • hBlockProj H n i eta with hxidef
    have hxi : ∀ i, xi i ∈ Vᗮ := fun i ↦
      Submodule.smul_mem _ _ (coord_mem_orthogonal V hetaperp i)
    have hd : (0:ℝ) ≤ (n:ℝ) * eps' := by positivity
    -- every entry is controlled
    have hentry : ∀ a ∈ insert (1 : ↥A) F, ∀ k l : Fin n,
        ‖⟪xi k, (a : H →L[ℂ] H) (xi l)⟫_ℂ - ⟪b k, rho a (b l)⟫_ℂ‖
          ≤ (n:ℝ) * eps' := by
      intro a ha k l
      have hu := hetaapprox (matrixUnit A a k l) (hGmem a ha k l)
      have hcoe : ((matrixUnit A a k l : ↥(ampSubalgebra A n)) :
          BlockSpace H n →L[ℂ] BlockSpace H n)
          = matrixUnitOp n (a : H →L[ℂ] H) k l := rfl
      have hst : ampState A hAclosed n b rho (matrixUnit A a k l)
          = ((n : ℂ))⁻¹ * ⟪b k, rho a (b l)⟫_ℂ :=
        ampStateLin_matrixUnit hn b rho a k l
      rw [hcoe, inner_matrixUnitOp, hst] at hu
      have hscale : ⟪xi k, (a : H →L[ℂ] H) (xi l)⟫_ℂ
          = (n : ℂ) * ⟪hBlockProj H n k eta,
              (a : H →L[ℂ] H) (hBlockProj H n l eta)⟫_ℂ := by
        rw [hxidef]
        simp only
        rw [inner_smul_left, map_smul, inner_smul_right, ← mul_assoc]
        simp only [Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN0]
        norm_cast
      have hsplit : ⟪xi k, (a : H →L[ℂ] H) (xi l)⟫_ℂ - ⟪b k, rho a (b l)⟫_ℂ
          = (n : ℂ) * (⟪hBlockProj H n k eta,
              (a : H →L[ℂ] H) (hBlockProj H n l eta)⟫_ℂ
                - ((n : ℂ))⁻¹ * ⟪b k, rho a (b l)⟫_ℂ) := by
        rw [hscale]
        field_simp
      rw [hsplit, norm_mul]
      have hnorm : ‖(n : ℂ)‖ = (n:ℝ) := by simp
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hu.le hN0
    -- the Gram clause
    have hgram : ∀ i j : Fin n,
        ‖⟪xi i, xi j⟫_ℂ - (if i = j then 1 else 0)‖ ≤ (n:ℝ) * eps' := by
      intro i j
      have h := hentry 1 (Finset.mem_insert_self _ _) i j
      have h1 : ((1 : ↥A) : H →L[ℂ] H) (xi j) = xi j := rfl
      have h2 : ⟪b i, rho 1 (b j)⟫_ℂ = if i = j then 1 else 0 := by
        rw [map_one]
        exact inner_one_entry b i j
      rwa [h1, h2] at h
    -- the two operator bounds
    have hbound : ∀ (y : H →L[ℂ] H) (R : K₀ →L[ℂ] K₀),
        (∀ i j, ‖⟪xi i, y (xi j)⟫_ℂ - ⟪b i, R (b j)⟫_ℂ‖ ≤ (n:ℝ) * eps') →
        ‖ContinuousLinearMap.adjoint (frameOfTuple b xi) ∘L frameOfTuple b xi - 1‖
            ≤ (n:ℝ) * ((n:ℝ) * ((n:ℝ) * eps')) ∧
          ‖ContinuousLinearMap.adjoint (frameOfTuple b xi) ∘L y ∘L frameOfTuple b xi
              - R‖ ≤ (n:ℝ) * ((n:ℝ) * ((n:ℝ) * eps')) := by
      intro y R hy
      obtain ⟨-, h1, h2⟩ :=
        frame_bounds_of_entries b xi Vᗮ hxi hd hgram y R hy
      rw [Fintype.card_fin] at h1 h2
      exact ⟨h1, h2⟩
    have hcube : (n:ℝ) * ((n:ℝ) * ((n:ℝ) * eps')) = (n:ℝ)^3 * eps' := by ring
    have hfinal : (n:ℝ) * ((n:ℝ) * ((n:ℝ) * eps')) < eps := by
      rw [hcube, ← hmul]
      nlinarith [heps'0, pow_nonneg hN0 3]
    refine ⟨frameOfTuple b xi, frameOfTuple_mem b xi Vᗮ hxi, ?_, ?_⟩
    · have hone : ∀ i j : Fin n,
          ‖⟪xi i, (1 : H →L[ℂ] H) (xi j)⟫_ℂ
            - ⟪b i, (1 : K₀ →L[ℂ] K₀) (b j)⟫_ℂ‖ ≤ (n:ℝ) * eps' := by
        intro i j
        have h1 : (1 : H →L[ℂ] H) (xi j) = xi j := rfl
        rw [h1, inner_one_entry b i j]
        exact hgram i j
      exact lt_of_le_of_lt (hbound 1 1 hone).1 hfinal
    · intro a ha
      exact lt_of_le_of_lt
        (hbound (a : H →L[ℂ] H) (rho a)
          (fun i j ↦ hentry a (Finset.mem_insert_of_mem ha) i j)).2 hfinal

/-- **(V3) closed against Glimm's lemma.**  The one-step approximation follows
from the frame, and the frame from Glimm. -/
theorem oneStepApproximation_of_glimm (hG : GlimmLemmaStatement) :
    OneStepApproximationStatement :=
  oneStep_of_frame (frameApproximation_of_glimm hG)

end

end ShulmanFill
end GroupApproximation
