import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftPrinted
import GroupApproximation.Analysis.ShulmanFillNormingScalarMF

/-!
# The printed-pair form of Theorem 4's lifting direction is false

`Theorem4PrintedPairStatement` (`Analysis/ShulmanFillNormingExistentialLiftPrinted`)
pins the coefficient algebras of `𝒟` to the printed family
`EllTwoCoefficient n = B(ℂ^{n+1})` and quantifies its Hilbert space `H` over
every separable one.  Pinning the sizes is what makes `hD` free, and it is also
what makes the statement false.  This module refutes it.

## The counter-model

`H = ℂ¹`.  For `n ≥ 1` there is no nonzero `*`-homomorphism
`B(ℂ^{n+1}) → B(ℂ¹)`, so `ι n 1 = 0` for every such `n` and the clause

    `hone : ∀ v, ι n (1 : EllTwoCoefficient n) v → v`

fails at every `v ≠ 0`.  The hypotheses are met: `B = C = ℂ` with `k = id`,
`IsMFAlgebra ℂ` from `hasMFEmbedding_complex`, and `ρ₁ = ρ₂` the scalar
representation, which is faithful and agrees with itself on `C`.

The vanishing needs no simplicity theory.  Transport the coefficient algebra to
matrices along `Matrix.toEuclideanCLM`.  In `B(ℂ¹)` products commute and there
is no nonzero square-zero element, so for `i ≠ j`

    `χ(eᵢᵢ) = χ(eᵢⱼ)χ(eⱼᵢ)` ,  `χ(eⱼⱼ) = χ(eⱼᵢ)χ(eᵢⱼ)` ,
    `χ(eᵢᵢ)χ(eⱼⱼ) = χ(eᵢᵢeⱼⱼ) = 0`

force `χ(eᵢᵢ)² = 0`, hence `χ(eᵢᵢ) = 0`; and `1 = ∑ᵢ eᵢᵢ`.  Two indices are
needed, which is why the argument starts at `n ≥ 1`.

## What this refutes and what it does not

Only the printed form.  `Theorem4RepresentationFirstStatement` and
`Theorem4TwoLegStatement` quantify their coefficient algebras existentially, so
a consumer facing `H = ℂ¹` may answer with the scalar model and this argument
has nothing to bite on.  The defect is the pinned sizes, not the vocabulary.

It is also not the only defect, so repairing `hone` alone does not save the
statement: the sup norm on `StarStrong.BoundedStarSequence` controls every fixed
coordinate, and at a finite-dimensional coefficient algebra that forces the
coordinate maps to converge to honest `*`-homomorphisms.  At `n = 0`, where the
coefficient is `B(ℂ¹)`, that is a character on `B`.  That second refutation is
the subject of `Analysis/ShulmanFillNormingPrintedPairCharacter`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section OneDimensional

/-- The one-dimensional Hilbert space the counter-model uses: the space the
printed models act on at `n = 0`. -/
abbrev OneDimSpace : Type := EuclideanSpace ℂ (Fin 1)

/-- The matrix picture of the operators on `ℂ¹`. -/
abbrev oneDimEquiv :
    Matrix (Fin 1) (Fin 1) ℂ ≃⋆ₐ[ℂ] (OneDimSpace →L[ℂ] OneDimSpace) :=
  Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℂ)

/-- Entries of a product of one-by-one matrices. -/
theorem mul_apply_fin_one (M N : Matrix (Fin 1) (Fin 1) ℂ) :
    (M * N) 0 0 = M 0 0 * N 0 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_one]

/-- A one-by-one matrix is determined by its single entry. -/
theorem matrix_fin_one_eq_zero {M : Matrix (Fin 1) (Fin 1) ℂ} (h : M 0 0 = 0) :
    M = 0 := by
  ext a b
  have ha : a = 0 := Subsingleton.elim a 0
  have hb : b = 0 := Subsingleton.elim b 0
  subst ha
  subst hb
  simpa using h

/-- **The operators on `ℂ¹` commute.** -/
theorem oneDim_mul_comm (S T : OneDimSpace →L[ℂ] OneDimSpace) : S * T = T * S := by
  obtain ⟨M, rfl⟩ : ∃ M, oneDimEquiv M = S := ⟨oneDimEquiv.symm S, by simp⟩
  obtain ⟨N, rfl⟩ : ∃ N, oneDimEquiv N = T := ⟨oneDimEquiv.symm T, by simp⟩
  have hMN : M * N = N * M := by
    ext a b
    have ha : a = 0 := Subsingleton.elim a 0
    have hb : b = 0 := Subsingleton.elim b 0
    subst ha
    subst hb
    rw [mul_apply_fin_one, mul_apply_fin_one, mul_comm]
  rw [← map_mul, ← map_mul, hMN]

/-- **The operators on `ℂ¹` have no nonzero square-zero element.** -/
theorem oneDim_eq_zero_of_mul_self (S : OneDimSpace →L[ℂ] OneDimSpace)
    (h : S * S = 0) : S = 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, oneDimEquiv M = S := ⟨oneDimEquiv.symm S, by simp⟩
  have hM : M * M = 0 := by
    refine oneDimEquiv.injective ?_
    rw [map_mul, map_zero]
    exact h
  have h00 : M 0 0 * M 0 0 = 0 := by
    have hentry : (M * M) 0 0 = (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 := by rw [hM]
    rw [mul_apply_fin_one] at hentry
    simpa using hentry
  rw [matrix_fin_one_eq_zero (mul_self_eq_zero.mp h00), map_zero]

/-- The identity of `B(ℂ¹)` is not zero. -/
theorem oneDim_one_ne_zero : (1 : OneDimSpace →L[ℂ] OneDimSpace) ≠ 0 := by
  intro h
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    have hsymm := congrArg oneDimEquiv.symm h
    rw [map_one, map_zero] at hsymm
    exact hsymm
  have hentry := congrArg (fun P : Matrix (Fin 1) (Fin 1) ℂ ↦ P 0 0) h1
  simp at hentry

end OneDimensional

section MatrixUnits

/-- The unit is the sum of the diagonal matrix units. -/
theorem one_eq_sum_single (k : ℕ) :
    (1 : Matrix (Fin k) (Fin k) ℂ) = ∑ i : Fin k, Matrix.single i i (1 : ℂ) := by
  ext a b
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    rw [Finset.sum_eq_single a]
    · rw [Matrix.single_apply_same, if_pos rfl]
    · intro i _ hi
      exact Matrix.single_apply_of_ne _ _ _ _ _ (by simp [hi])
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨rfl, rfl⟩
    exact h rfl

end MatrixUnits

section NoRepresentation

/-- **A `*`-homomorphism of a printed coefficient algebra of size at least two
into the operators on `ℂ¹` kills the unit.**

The diagonal matrix units are pairwise orthogonal and pairwise equivalent, and
the target is commutative with no nonzero square-zero element, so every one of
them is killed; the unit is their sum. -/
theorem ellTwoHom_one_eq_zero {k : ℕ}
    (chi : EllTwoCoefficient (k + 1) →⋆ₙₐ[ℂ] (OneDimSpace →L[ℂ] OneDimSpace)) :
    chi 1 = 0 := by
  have e : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ ≃⋆ₐ[ℂ] EllTwoCoefficient (k + 1) :=
    Matrix.toEuclideanCLM (n := Fin (k + 2)) (𝕜 := ℂ)
  have hdiag : ∀ i : Fin (k + 2), chi (e (Matrix.single i i 1)) = 0 := by
    intro i
    obtain ⟨j, hji⟩ := exists_ne i
    have hij : i ≠ j := Ne.symm hji
    have h1 : Matrix.single i j (1 : ℂ) * Matrix.single j i 1
        = Matrix.single i i 1 := by simp
    have h2 : Matrix.single j i (1 : ℂ) * Matrix.single i j 1
        = Matrix.single j j 1 := by simp
    have h3 : Matrix.single i i (1 : ℂ) * Matrix.single j j 1 = 0 := by
      simp [hij]
    have hii : chi (e (Matrix.single i i 1))
        = chi (e (Matrix.single i j 1)) * chi (e (Matrix.single j i 1)) := by
      rw [← map_mul, ← map_mul, h1]
    have hjj : chi (e (Matrix.single j j 1))
        = chi (e (Matrix.single j i 1)) * chi (e (Matrix.single i j 1)) := by
      rw [← map_mul, ← map_mul, h2]
    have horth : chi (e (Matrix.single i i 1)) * chi (e (Matrix.single j j 1))
        = 0 := by
      rw [← map_mul, ← map_mul, h3, map_zero, map_zero]
    rw [hii, hjj, oneDim_mul_comm (chi (e (Matrix.single j i 1)))] at horth
    rw [hii]
    exact oneDim_eq_zero_of_mul_self _ horth
  have hsum : (1 : EllTwoCoefficient (k + 1))
      = ∑ i : Fin (k + 2), e (Matrix.single i i 1) := by
    rw [← map_sum, ← one_eq_sum_single (k + 2), map_one]
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hdiag i

end NoRepresentation

section ScalarRepresentation

/-- The scalars, represented on `ℂ¹`. -/
def scalarRepOne : ℂ →⋆ₐ[ℂ] (OneDimSpace →L[ℂ] OneDimSpace) where
  toFun z := z • (1 : OneDimSpace →L[ℂ] OneDimSpace)
  map_one' := one_smul ℂ _
  map_mul' a b := by
    rw [smul_mul_smul_comm, mul_one]
  map_zero' := zero_smul ℂ (1 : OneDimSpace →L[ℂ] OneDimSpace)
  map_add' a b := add_smul a b (1 : OneDimSpace →L[ℂ] OneDimSpace)
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' z := by
    rw [star_smul, star_one]

/-- **The scalar representation is faithful.**  Read off the unit rather than
off the definition: a scalar in the kernel has an inverse, and a unital
`*`-homomorphism cannot kill the unit of `B(ℂ¹)`. -/
theorem scalarRepOne_injective : Function.Injective scalarRepOne := by
  intro a b hab
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h0 : scalarRepOne (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h1 : scalarRepOne ((a - b)⁻¹ * (a - b)) = 0 := by
    rw [map_mul, h0, mul_zero]
  rw [inv_mul_cancel₀ hd, map_one] at h1
  exact oneDim_one_ne_zero h1

end ScalarRepresentation

section Refutation

/-- The scalars are MF. -/
theorem isMFAlgebra_complex : IsMFAlgebra ℂ :=
  ⟨inferInstance, hasMFEmbedding_complex⟩

/-- **The printed-pair form of Theorem 4's lifting direction is false.**

At `H = ℂ¹` the printed models have nowhere to go: `ellTwoHom_one_eq_zero`
kills `ι n 1` for every `n ≥ 1`, so `hone` cannot hold. -/
theorem not_theorem4PrintedPair : ¬ Theorem4PrintedPairStatement := by
  intro h
  obtain ⟨ι, _hnorm, hone, _hlift₁, _hlift₂, _hagree⟩ :=
    h (H := OneDimSpace) (C := ℂ) (B := ℂ) (StarAlgHom.id ℂ ℂ) isMFAlgebra_complex
      scalarRepOne scalarRepOne scalarRepOne_injective scalarRepOne_injective rfl
  obtain ⟨v, hv⟩ := exists_ne (0 : OneDimSpace)
  have hzero : (fun _ : ℕ ↦ (0 : OneDimSpace))
      =ᶠ[atTop] fun n ↦ ι n (1 : EllTwoCoefficient n) v := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
      ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
    rw [ellTwoHom_one_eq_zero (ι (k + 1))]
    rfl
  have hlim : Tendsto (fun n ↦ ι n (1 : EllTwoCoefficient n) v) atTop (𝓝 0) :=
    Tendsto.congr' hzero tendsto_const_nhds
  exact hv (tendsto_nhds_unique (hone v) hlim)

end Refutation

end

end ShulmanFill
end GroupApproximation
