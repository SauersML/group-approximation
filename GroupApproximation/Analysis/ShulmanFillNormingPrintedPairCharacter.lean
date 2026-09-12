import GroupApproximation.Analysis.MFAlgebraMatrixAmplification
import GroupApproximation.Analysis.ShulmanFillNormingPrintedPairRefuted
import GroupApproximation.Analysis.ShulmanFillNormingResiduallyFinite

/-!
# The printed-pair form forces a character, and so fails at every `H`

`Analysis/ShulmanFillNormingPrintedPairRefuted` refutes
`Theorem4PrintedPairStatement` at a one-dimensional `H`, where the printed
models have nowhere to go.  That defect is about `hone` and could be legislated
away by asking `H` to be infinite-dimensional.  This module shows that the
statement would still be false, for a reason that has nothing to do with `H`.

## The obstruction

`StarStrong.BoundedStarSequence A` is `lp _ ∞`, so its norm is the supremum
over coordinates and every fixed coordinate is controlled by it: the module
docstring of `Analysis/ShulmanFillNormingAsymptotic` says as much, that "all
four defects are measured in the product norm".  Fix a coordinate `n` and put
`ψ_t = (φ_t ·)ₙ : B → A n`.  Then `ψ_t` is contractive and its additivity,
homogeneity, multiplicativity, adjoint and unit defects all vanish as `t → ∞`.

If `A n` is finite-dimensional — and the printed `A n = B(ℂ^{n+1})` is — bounded
sets in it are compact, so the limit of `ψ_t` along an ultrafilter refining
`atTop` exists at every point of `B`.  Uniqueness of limits turns each vanishing
defect into an identity, and the limit is an honest unital `*`-homomorphism
`B → A n`.  No separability and no diagonal extraction is needed: the ultrafilter
does that work.

At `n = 0` the printed coefficient is `B(ℂ¹)`, so this is a character on `B`,
and `Analysis/ShulmanFillNormingPrintedPairRefuted.ellTwoHom_one_eq_zero` says
`B(ℂ²)` has none.  `B = B(ℂ²)` acting on `H = ℂ²` by the identity is separable
and MF, so the statement fails there too.

## What this says about the vocabulary

The asymptotic vocabulary was introduced to escape the coordinate obstruction of
`Analysis/ShulmanFillNormingResiduallyFinite`, whose header says asymptotic
multiplicativity "is exactly what the coordinate argument above cannot exploit,
because `φ_t` composed with a coordinate is not a homomorphism".  That is true
of each single `φ_t` and false of the family: the limit over `t` is a
homomorphism whenever the coordinate algebra is finite-dimensional.  So an
asymptotic-lift binder escapes the obstruction only if its coefficients are
infinite-dimensional, or if its defects are measured in the reduced product
rather than in the sup norm.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u v

section CoordinateLimit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {B : Type v} [CStarAlgebra B] {π : B →⋆ₐ[ℂ] (H →L[ℂ] H)}

/-- The `n`-th coordinate of the `t`-th map of an asymptotic lift. -/
def coordFun (φ : StarStrongAsymptoticLift ι hnorm hone π) (n t : ℕ) (b : B) : A n :=
  boundedStarSequenceCoord n (φ.toFun t b)

@[simp] theorem coordFun_apply (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (n t : ℕ) (b : B) :
    coordFun φ n t b = boundedStarSequenceCoord n (φ.toFun t b) := rfl

/-- Each coordinate map is contractive. -/
theorem norm_coordFun_le (φ : StarStrongAsymptoticLift ι hnorm hone π)
    (n t : ℕ) (b : B) : ‖coordFun φ n t b‖ ≤ ‖b‖ :=
  φ.norm_coord_le t b n

/-- A defect measured in the product norm is a defect at every coordinate. -/
theorem tendsto_norm_coord_of_tendsto (n : ℕ)
    {Y : ℕ → StarStrong.BoundedStarSequence A}
    (h : Tendsto (fun t ↦ ‖Y t‖) atTop (𝓝 0)) :
    Tendsto (fun t ↦ ‖boundedStarSequenceCoord n (Y t)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun t ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero (Y t) n) h

/-- **A fixed coordinate of an asymptotic lift is an honest unital
`*`-homomorphism in the limit**, as soon as that coordinate algebra is proper —
which a finite-dimensional one is.

The limit is taken along an ultrafilter refining `atTop`, so no separability of
`B` and no diagonal extraction is needed; every vanishing defect becomes an
identity by uniqueness of limits. -/
theorem exists_nonUnitalStarAlgHom_coord
    (φ : StarStrongAsymptoticLift ι hnorm hone π) (n : ℕ) [ProperSpace (A n)] :
    ∃ ψ : B →⋆ₙₐ[ℂ] A n, ψ 1 = 1 := by
  classical
  have hU : ((Ultrafilter.of (atTop : Filter ℕ)) : Filter ℕ) ≤ atTop :=
    Ultrafilter.of_le atTop
  set U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hex : ∀ b : B, ∃ x : A n,
      Tendsto (fun t ↦ coordFun φ n t b) (U : Filter ℕ) (𝓝 x) := by
    intro b
    have hmem : ∀ t : ℕ, coordFun φ n t b ∈ Metric.closedBall (0 : A n) ‖b‖ := by
      intro t
      simpa [Metric.mem_closedBall, dist_zero_right] using norm_coordFun_le φ n t b
    obtain ⟨x, -, hx⟩ :=
      (isCompact_closedBall (0 : A n) ‖b‖).ultrafilter_le_nhds
        (U.map fun t ↦ coordFun φ n t b)
        (by
          rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
          exact Filter.univ_mem' hmem)
    exact ⟨x, hx⟩
  choose f hf using hex
  have hdefect : ∀ (Y : ℕ → StarStrong.BoundedStarSequence A),
      Tendsto (fun t ↦ ‖Y t‖) atTop (𝓝 0) →
      Tendsto (fun t ↦ boundedStarSequenceCoord n (Y t)) (U : Filter ℕ) (𝓝 0) := by
    intro Y hY
    exact Tendsto.mono_left
      (tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_coord_of_tendsto n hY)) hU
  have hadd : ∀ b c : B, f (b + c) = f b + f c := by
    intro b c
    have h0 := hdefect (fun t ↦ φ.toFun t (b + c) - φ.toFun t b - φ.toFun t c)
      (φ.tendsto_add b c)
    have h1 : Tendsto
        (fun t ↦ coordFun φ n t (b + c) - (coordFun φ n t b + coordFun φ n t c))
        (U : Filter ℕ) (𝓝 0) := by
      simpa [map_sub, sub_sub] using h0
    have h2 := (hf (b + c)).sub ((hf b).add (hf c))
    exact sub_eq_zero.mp (tendsto_nhds_unique h2 h1)
  have hsmul : ∀ (c : ℂ) (b : B), f (c • b) = c • f b := by
    intro c b
    have h0 := hdefect (fun t ↦ φ.toFun t (c • b) - c • φ.toFun t b)
      (φ.tendsto_smul c b)
    have h1 : Tendsto (fun t ↦ coordFun φ n t (c • b) - c • coordFun φ n t b)
        (U : Filter ℕ) (𝓝 0) := by
      simpa [map_sub, map_smul] using h0
    have h2 := (hf (c • b)).sub ((hf b).const_smul c)
    exact sub_eq_zero.mp (tendsto_nhds_unique h2 h1)
  have hmul : ∀ b c : B, f (b * c) = f b * f c := by
    intro b c
    have h0 := hdefect (fun t ↦ φ.toFun t (b * c) - φ.toFun t b * φ.toFun t c)
      (φ.tendsto_mul b c)
    have h1 : Tendsto
        (fun t ↦ coordFun φ n t (b * c) - coordFun φ n t b * coordFun φ n t c)
        (U : Filter ℕ) (𝓝 0) := by
      simpa [map_sub, map_mul] using h0
    have h2 := (hf (b * c)).sub ((hf b).mul (hf c))
    exact sub_eq_zero.mp (tendsto_nhds_unique h2 h1)
  have hstar : ∀ b : B, f (star b) = star (f b) := by
    intro b
    have h0 := hdefect (fun t ↦ φ.toFun t (star b) - star (φ.toFun t b))
      (φ.tendsto_star b)
    have h1 : Tendsto (fun t ↦ coordFun φ n t (star b) - star (coordFun φ n t b))
        (U : Filter ℕ) (𝓝 0) := by
      simpa [map_sub, map_star] using h0
    have h2 := (hf (star b)).sub (hf b).star
    exact sub_eq_zero.mp (tendsto_nhds_unique h2 h1)
  have hzero : f 0 = 0 := by
    have hz : ∀ t : ℕ, coordFun φ n t 0 = 0 := by
      intro t
      have hle : ‖φ.toFun t (0 : B)‖ ≤ 0 := by simpa using φ.norm_le t 0
      have : φ.toFun t (0 : B) = 0 := norm_le_zero_iff.mp hle
      rw [coordFun_apply, this, map_zero]
    have h2 : Tendsto (fun t ↦ coordFun φ n t 0) (U : Filter ℕ) (𝓝 0) := by
      have hfun : (fun t ↦ coordFun φ n t (0 : B)) = fun _ : ℕ ↦ (0 : A n) := funext hz
      rw [hfun]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hf 0) h2
  have honef : f 1 = 1 := by
    have h0 := hdefect (fun t ↦ φ.toFun t 1 - 1) φ.tendsto_one
    have h1 : Tendsto (fun t ↦ coordFun φ n t 1 - 1) (U : Filter ℕ) (𝓝 0) := by
      simpa [map_sub, map_one] using h0
    have h2 := (hf 1).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : A n)) (U : Filter ℕ) (𝓝 1))
    exact sub_eq_zero.mp (tendsto_nhds_unique h2 h1)
  exact ⟨{ toFun := f
           map_smul' := hsmul
           map_zero' := hzero
           map_add' := hadd
           map_mul' := hmul
           map_star' := hstar }, honef⟩

end CoordinateLimit

section Witness

/-- The identity of a printed coefficient algebra is nonzero. -/
theorem ellTwo_one_ne_zero (n : ℕ) : (1 : EllTwoCoefficient n) ≠ 0 := by
  intro h
  have e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ≃⋆ₐ[ℂ] EllTwoCoefficient n :=
    Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)
  have h1 : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 0 := by
    have hs := congrArg e.symm h
    rw [map_one, map_zero] at hs
    exact hs
  have hentry :=
    congrArg (fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ↦ P 0 0) h1
  simp at hentry

/-- The printed coefficient algebras are nontrivial. -/
theorem nontrivial_ellTwoCoefficient (n : ℕ) : Nontrivial (EllTwoCoefficient n) :=
  ⟨1, 0, ellTwo_one_ne_zero n⟩

/-- `B(ℂ²)` is a matrix algebra, in the form `HasMFEmbedding` consumes. -/
theorem hasMFEmbedding_ellTwoCoefficient_one :
    HasMFEmbedding (EllTwoCoefficient 1) := by
  have e : EllTwoCoefficient 1 ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ :=
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm.trans
      CStarMatrix.ofMatrixStarAlgEquiv
  exact HasMFEmbedding.of_injective_nonUnitalStarAlgHom
    (MFAlgebraMatrixAmplification.hasMFEmbedding_cstarMatrix 2 hasMFEmbedding_complex)
    e.toNonUnitalStarAlgHom e.injective

/-- `B(ℂ²)` is separable and MF. -/
theorem isMFAlgebra_ellTwoCoefficient_one : IsMFAlgebra (EllTwoCoefficient 1) :=
  ⟨inferInstance, hasMFEmbedding_ellTwoCoefficient_one⟩

end Witness

section CharacterRefutation

/-- **The printed-pair form of Theorem 4's lifting direction is false a second
time**, at an `H` of any dimension: it forces a character on every separable MF
algebra it is applied to, and `B(ℂ²)` has none.

Unlike `not_theorem4PrintedPair`, nothing here is about the size of `H`; the
witness is `H = ℂ²` with `B = B(ℂ²)` acting on it by the identity. -/
theorem not_theorem4PrintedPair_of_character : ¬ Theorem4PrintedPairStatement := by
  intro h
  haveI : ∀ n, Nontrivial (EllTwoCoefficient n) := nontrivial_ellTwoCoefficient
  haveI : ProperSpace (EllTwoCoefficient 0) := FiniteDimensional.proper ℂ (EllTwoCoefficient 0)
  obtain ⟨ι, _hnorm, _hone, φ₁, _hlift₂, _hagree⟩ :=
    h (H := EuclideanSpace ℂ (Fin 2)) (C := EllTwoCoefficient 1)
      (B := EllTwoCoefficient 1) (StarAlgHom.id ℂ (EllTwoCoefficient 1))
      isMFAlgebra_ellTwoCoefficient_one
      (StarAlgHom.id ℂ (EllTwoCoefficient 1)) (StarAlgHom.id ℂ (EllTwoCoefficient 1))
      Function.injective_id Function.injective_id rfl
  obtain ⟨ψ, hψ⟩ := exists_nonUnitalStarAlgHom_coord φ₁ 0
  have hzero : ψ 1 = 0 := ellTwoHom_one_eq_zero (k := 0) ψ
  rw [hψ] at hzero
  exact ellTwo_one_ne_zero 0 hzero

end CharacterRefutation

end

end ShulmanFill
end GroupApproximation
