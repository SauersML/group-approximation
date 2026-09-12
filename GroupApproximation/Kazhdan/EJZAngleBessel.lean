import GroupApproximation.Kazhdan.EJZAngleTranslates

/-!
# Bessel's inequality for translate sums over transversal cyclic subgroups

Input to the representation angle `√(2/p)` of the Sylow subgroup `U₄(p)` of `Sp₄(F_p)`
(Caprace--Conder--Kaluba--Witzel, arXiv:2011.09276, Proposition 7.3(ii)), proved without characters.

* `sum_norm_sq_translateSum_le`: let `tᵢ` (`i ∈ S`) be pairwise commuting elements of exponent `p`,
  commuting with `z`, such that a vector fixed by two distinct `tᵢ, tⱼ` is fixed by `z`.  Then for
  `x` orthogonal to the `z`-fixed vectors, `∑ᵢ ‖∑_{k<p} ρ(tᵢᵏ) x‖² ≤ p² ‖x‖²`.  The translate sums
  are pairwise orthogonal and each pairs with `x` as a third of its squared norm divided by `p`.
* Coordinates in `⟨w, z⟩` for commuting `w, z` of exponent `p`: powers and products of
  `wⁱ zʲ` add exponents, and `z` is a word in two such elements when a linear system mod `p` is
  solvable (`fixed_of_two_coordinates`).
-/

namespace GroupApproximation

universe u v

namespace EJZAngleBessel

open EJZAngleTranslates

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Moving an isometry from one side of the inner product to the other. -/
theorem inner_apply_left (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (h : G) (x g : E) :
    inner ℝ (ρ h x) g = inner ℝ x (ρ h⁻¹ g) := by
  have hg : ρ h (ρ h⁻¹ g) = g := by
    have h1 := congrArg (fun q ↦ ρ q g) (mul_inv_cancel h)
    simp only [map_mul, map_one] at h1
    exact h1
  calc
    inner ℝ (ρ h x) g = inner ℝ (ρ h x) (ρ h (ρ h⁻¹ g)) := by rw [hg]
    _ = inner ℝ x (ρ h⁻¹ g) := LinearIsometryEquiv.inner_map_map _ _ _

/-- **Bessel's inequality for translate sums over transversal cyclic subgroups.** -/
theorem sum_norm_sq_translateSum_le (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {ι : Type*} {p : ℕ} (hp0 : 0 < p)
    (S : Finset ι) (t : ι → G) (z : G) (ht : ∀ i ∈ S, t i ^ p = 1)
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute (t i) (t j)) (htz : ∀ i ∈ S, Commute (t i) z)
    (hgen : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ v : E, ρ (t i) v = v → ρ (t j) v = v → ρ z v = v)
    {x : E} (hx : ∀ g : E, ρ z g = g → inner ℝ x g = 0) :
    ∑ i ∈ S, ‖translateSum ρ (t i) p x‖ ^ 2 ≤ (p : ℝ) ^ 2 * ‖x‖ ^ 2 := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp0
  -- each translate sum is orthogonal to the `z`-fixed vectors
  have hTz : ∀ i ∈ S, ∀ g : E, ρ z g = g → inner ℝ (translateSum ρ (t i) p x) g = 0 := by
    intro i hi g hg
    unfold translateSum
    rw [sum_inner]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [inner_apply_left]
    apply hx
    have hc : Commute ((t i ^ k)⁻¹) z := ((htz i hi).pow_left k).inv_left
    have h := congrArg (fun q ↦ ρ q g) hc.eq
    simp only [map_mul] at h
    change ρ ((t i ^ k)⁻¹) (ρ z g) = ρ z (ρ ((t i ^ k)⁻¹) g) at h
    rw [hg] at h
    exact h.symm
  -- pairwise orthogonality
  have horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      inner ℝ (translateSum ρ (t i) p x) (translateSum ρ (t j) p x) = 0 := by
    intro i hi j hj hij
    set Ti := translateSum ρ (t i) p x
    set Tj := translateSum ρ (t j) p x
    have hTi_fix : ρ (t i) Ti = Ti := translateSum_fixed ρ (ht i hi) x
    have hTj_fix : ρ (t j) Tj = Tj := translateSum_fixed ρ (ht j hj) x
    have hU_i : ρ (t i) (translateSum ρ (t i) p Tj) = translateSum ρ (t i) p Tj :=
      translateSum_fixed ρ (ht i hi) Tj
    have hU_j : ρ (t j) (translateSum ρ (t i) p Tj) = translateSum ρ (t i) p Tj := by
      unfold translateSum
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have h := congrArg (fun q ↦ ρ q Tj) ((hcomm i hi j hj).pow_left k).eq
      simp only [map_mul] at h
      change ρ (t i ^ k) (ρ (t j) Tj) = ρ (t j) (ρ (t i ^ k) Tj) at h
      rw [hTj_fix] at h
      exact h.symm
    have hUz := hgen i hi j hj hij _ hU_i hU_j
    have h0 : inner ℝ Ti (translateSum ρ (t i) p Tj) = 0 := hTz i hi _ hUz
    rw [real_inner_comm, inner_translateSum_of_fixed ρ (t i) p Tj hTi_fix] at h0
    have hp' : (p : ℝ) ≠ 0 := hppos.ne'
    have := (mul_eq_zero.mp h0).resolve_left hp'
    rw [real_inner_comm]
    exact this
  -- `p ⟪Tᵢ, x⟫ = ‖Tᵢ‖²`
  have hTx : ∀ i ∈ S, (p : ℝ) * inner ℝ (translateSum ρ (t i) p x) x =
      ‖translateSum ρ (t i) p x‖ ^ 2 := by
    intro i hi
    rw [norm_sq_translateSum ρ (ht i hi) x, real_inner_comm]
    unfold translateSum
    rw [inner_sum]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ i ∈ S, ‖translateSum ρ (t i) p x‖ ^ 2 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hYY : ‖∑ i ∈ S, translateSum ρ (t i) p x‖ ^ 2 = A := by
    rw [← real_inner_self_eq_norm_sq, sum_inner, hA]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [inner_sum, Finset.sum_eq_single i (fun j hj hji ↦ horth i hi j hj hji.symm)
      (fun h ↦ absurd hi h), real_inner_self_eq_norm_sq]
  have hYx : (p : ℝ) * inner ℝ (∑ i ∈ S, translateSum ρ (t i) p x) x = A := by
    rw [sum_inner, Finset.mul_sum, hA]
    exact Finset.sum_congr rfl fun i hi ↦ hTx i hi
  have hcs := real_inner_le_norm (∑ i ∈ S, translateSum ρ (t i) p x) x
  have hle : A ≤ (p : ℝ) * (‖∑ i ∈ S, translateSum ρ (t i) p x‖ * ‖x‖) := by
    rw [← hYx]
    exact mul_le_mul_of_nonneg_left hcs hppos.le
  have hsq : A ^ 2 ≤ (p : ℝ) ^ 2 * A * ‖x‖ ^ 2 := by
    have h1 := pow_le_pow_left₀ hA0 hle 2
    calc
      A ^ 2 ≤ ((p : ℝ) * (‖∑ i ∈ S, translateSum ρ (t i) p x‖ * ‖x‖)) ^ 2 := h1
      _ = (p : ℝ) ^ 2 * ‖∑ i ∈ S, translateSum ρ (t i) p x‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ = (p : ℝ) ^ 2 * A * ‖x‖ ^ 2 := by rw [hYY]
  rw [← hA]
  rcases hA0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

/-! ### Coordinates in `⟨w, z⟩` -/

section Coordinates

variable {w z : G}

/-- Powers of `wⁱ zʲ` multiply the exponents. -/
theorem coord_pow (hwz : Commute w z) (i j k : ℕ) :
    (w ^ i * z ^ j) ^ k = w ^ (i * k) * z ^ (j * k) := by
  rw [(hwz.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul]

/-- Products of `wⁱ zʲ` add the exponents. -/
theorem coord_mul (hwz : Commute w z) (i j i' j' : ℕ) :
    (w ^ i * z ^ j) * (w ^ i' * z ^ j') = w ^ (i + i') * z ^ (j + j') := by
  have h : z ^ j * w ^ i' = w ^ i' * z ^ j := ((hwz.pow_pow i' j).eq).symm
  calc
    (w ^ i * z ^ j) * (w ^ i' * z ^ j') = w ^ i * (z ^ j * w ^ i') * z ^ j' := by
      simp only [mul_assoc]
    _ = w ^ i * (w ^ i' * z ^ j) * z ^ j' := by rw [h]
    _ = w ^ (i + i') * z ^ (j + j') := by rw [pow_add, pow_add]; simp only [mul_assoc]

/-- Elements of the form `wⁱ zʲ` commute with each other. -/
theorem coord_commute (hwz : Commute w z) (i j i' j' : ℕ) :
    Commute (w ^ i * z ^ j) (w ^ i' * z ^ j') := by
  unfold Commute SemiconjBy
  rw [coord_mul hwz, coord_mul hwz, add_comm i, add_comm j]

/-- Exponent `p` kills `wⁱ zʲ` when it kills `w` and `z`. -/
theorem coord_pow_p {p : ℕ} (hwz : Commute w z) (hw : w ^ p = 1) (hz : z ^ p = 1) (i j : ℕ) :
    (w ^ i * z ^ j) ^ p = 1 := by
  rw [coord_pow hwz, mul_comm i, mul_comm j, pow_mul, pow_mul, hw, hz, one_pow, one_pow, mul_one]

/-- **`z` is a word in two coordinates.**  If `(iα + i'β) mod p = 0` and `(jα + j'β) mod p = 1`,
a vector fixed by `wⁱ zʲ` and by `w^{i'} z^{j'}` is fixed by `z`. -/
theorem fixed_of_two_coordinates (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {p : ℕ} (hwz : Commute w z)
    (hw : w ^ p = 1) (hz : z ^ p = 1) {i j i' j' α β : ℕ}
    (h0 : (i * α + i' * β) % p = 0) (h1 : (j * α + j' * β) % p = 1) {v : E}
    (hv : ρ (w ^ i * z ^ j) v = v) (hv' : ρ (w ^ i' * z ^ j') v = v) : ρ z v = v := by
  have hword : (w ^ i * z ^ j) ^ α * (w ^ i' * z ^ j') ^ β = z := by
    rw [coord_pow hwz, coord_pow hwz, coord_mul hwz, pow_eq_pow_mod _ hw, pow_eq_pow_mod _ hz,
      h0, h1, pow_zero, pow_one, one_mul]
  rw [← hword, map_mul]
  change ρ ((w ^ i * z ^ j) ^ α) (ρ ((w ^ i' * z ^ j') ^ β) v) = v
  rw [pow_apply_of_fixed ρ hv' β, pow_apply_of_fixed ρ hv α]

end Coordinates

end EJZAngleBessel
end GroupApproximation

#audit_axioms GroupApproximation.EJZAngleBessel.inner_apply_left
#audit_axioms GroupApproximation.EJZAngleBessel.sum_norm_sq_translateSum_le
#audit_axioms GroupApproximation.EJZAngleBessel.coord_pow
#audit_axioms GroupApproximation.EJZAngleBessel.coord_mul
#audit_axioms GroupApproximation.EJZAngleBessel.coord_commute
#audit_axioms GroupApproximation.EJZAngleBessel.coord_pow_p
#audit_axioms GroupApproximation.EJZAngleBessel.fixed_of_two_coordinates
