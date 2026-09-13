import GroupApproximation.XCVWitness.ShiftOrthogonal

/-!
# Kishimoto's condition for a Bernoulli shift

`kishimotoCondition_of_shiftModel`: let `P` be a covariant expectation of `D` over a shift model
`C = ⊗_{j∈ℤ} Z`, where the unitary `u` implements the shift. If `Z` has norm-one elements `g, h`
with `h⋆g = 0`, then Kishimoto's condition holds.

The proof:
* Approximate `b₀` and the finitely many `bₙ` within `ε/2` by elements of a central block `[-M, M]`.
* Let `N` bound `|n|` for `n ∈ s`, and put `F = g_{M+1} · h_{M+2} ⋯ h_{M+N+1}`. It has norm one and
  lies in `block [M+1, ∞)`.
* So `F` commutes with the approximants and multiplies their norms. Hence `‖F⋆ b₀' F‖ = ‖b₀'‖`.
* `F⋆ bₙ' shiftₙ(F) = bₙ' · F⋆ shiftₙ(F) = 0` (`ShiftModel.star_mul_shift_eq_zero`).

`isSimpleCStar_of_shiftModel` combines this with `isSimpleCStar_of_kishimoto`.
-/

namespace GroupApproximation
namespace XCVWitness

variable {Z C D : Type*} [CStarAlgebra Z] [CStarAlgebra C] [CStarAlgebra D]

/-- Compression by two contractions does not increase the norm. -/
theorem norm_mul_mul_le_of_le_one {A : Type*} [CStarAlgebra A] {x y : A} (hx : ‖x‖ ≤ 1)
    (hy : ‖y‖ ≤ 1) (z : A) : ‖x * z * y‖ ≤ ‖z‖ := by
  calc ‖x * z * y‖ ≤ ‖x * z‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ ‖x * z‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = ‖x * z‖ := mul_one _
    _ ≤ ‖x‖ * ‖z‖ := norm_mul_le _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖z‖ := one_mul _

/-- **Kishimoto's condition for a Bernoulli shift.** -/
theorem kishimotoCondition_of_shiftModel (S : ShiftModel Z C) (P : CovariantExpectation C D)
    (hcov : ∀ (n : ℤ) (c : C),
      ((P.u ^ n : unitary D) : D) * P.ι c = P.ι (S.shift n c) * ((P.u ^ n : unitary D) : D))
    {g h : Z} (hg : ‖g‖ = 1) (hh : ‖h‖ = 1) (hhg : star h * g = 0) : KishimotoCondition P := by
  intro b₀ s b ε hε hs
  choose Mc c' hmem happ using fun c : C => S.dense c (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Mc b₀ ⊔ s.sup fun n => Mc (b n) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = s.sup Int.natAbs := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : C, F = S.coord ((M : ℤ) + 1) g * S.hprod h ((M : ℤ) + 1 + 1) N :=
    ⟨_, rfl⟩
  have hF1 : ‖F‖ = 1 := by rw [hFdef]; exact S.norm_coord_mul_hprod hg hh _ N
  have hFmem : F ∈ S.block (Set.Ici ((M : ℤ) + 1)) := by
    rw [hFdef]; exact S.coord_mul_hprod_mem g h _ N
  have hdisj : Disjoint (Set.Icc (-(M : ℤ)) M) (Set.Ici ((M : ℤ) + 1)) :=
    Set.disjoint_left.2 fun x hx hx' => by
      obtain ⟨hx1, hx2⟩ := Set.mem_Icc.1 hx
      rw [Set.mem_Ici] at hx'
      omega
  have hcen : ∀ c : C, Mc c ≤ M → c' c ∈ S.block (Set.Icc (-(M : ℤ)) M) := fun c hc =>
    S.block_mono (fun x hx => by
      obtain ⟨hx1, hx2⟩ := Set.mem_Icc.1 hx
      exact Set.mem_Icc.2 ⟨by omega, by omega⟩) _ (hmem c)
  have hcomm : ∀ c : C, Mc c ≤ M → Commute (c' c) (star F) := fun c hc =>
    S.commute_of_disjoint hdisj _ (hcen c hc) _ (star_mem hFmem)
  refine ⟨F, hF1.le, ?_, fun n hn => ?_⟩
  · have hle : Mc b₀ ≤ M := by rw [hM]; exact le_sup_left
    have hcen0 : star F * c' b₀ * F = c' b₀ * (star F * F) := by
      rw [← (hcomm b₀ hle).eq, mul_assoc]
    have hnorm0 : ‖star F * c' b₀ * F‖ = ‖c' b₀‖ := by
      rw [hcen0, S.norm_mul_of_disjoint hdisj _ (hcen b₀ hle) _ (mul_mem (star_mem hFmem) hFmem),
        CStarRing.norm_star_mul_self, hF1, mul_one, mul_one]
    have hsplit : star F * c' b₀ * F = star F * b₀ * F + star F * (c' b₀ - b₀) * F := by
      simp only [mul_sub, sub_mul]
      abel
    have h1 := norm_add_le (star F * b₀ * F) (star F * (c' b₀ - b₀) * F)
    rw [← hsplit, hnorm0] at h1
    have h2 := norm_star_mul_mul_le hF1.le (c' b₀ - b₀)
    have h3 := norm_sub_norm_le b₀ (c' b₀)
    have h4 : ‖c' b₀ - b₀‖ = ‖b₀ - c' b₀‖ := norm_sub_rev _ _
    have h5 := happ b₀
    linarith
  · have hn0 := hs n hn
    have hle : Mc (b n) ≤ M := by
      rw [hM]; exact le_sup_of_le_right (Finset.le_sup (f := fun n => Mc (b n)) hn)
    have hNn : n.natAbs ≤ N := by rw [hN]; exact Finset.le_sup (f := Int.natAbs) hn
    have hi : n.natAbs - 1 < N := by
      rcases Int.natAbs_eq n with h' | h' <;> omega
    have hzero : star F * S.shift n F = 0 := by
      have hpos := S.star_mul_shift_eq_zero hhg ((M : ℤ) + 1) N (n.natAbs - 1) hi
      rw [← hFdef] at hpos
      rcases Int.natAbs_eq n with h' | h'
      · have hni : ((n.natAbs - 1 : ℕ) : ℤ) + 1 = n := by omega
        rwa [hni] at hpos
      · have hni : ((n.natAbs - 1 : ℕ) : ℤ) + 1 = -n := by omega
        rw [hni] at hpos
        have hneg := S.star_mul_shift_neg hpos
        rwa [neg_neg] at hneg
    have hkill : star F * c' (b n) * S.shift n F = 0 := by
      rw [← (hcomm (b n) hle).eq, mul_assoc, hzero, mul_zero]
    have hsub : star F * (b n - c' (b n)) * S.shift n F = star F * b n * S.shift n F := by
      rw [mul_sub, sub_mul, hkill, sub_zero]
    have hrew : P.ι (star F) * (P.ι (b n) * ((P.u ^ n : unitary D) : D)) * P.ι F =
        P.ι (star F * (b n - c' (b n)) * S.shift n F) * ((P.u ^ n : unitary D) : D) := by
      rw [hsub, map_mul, map_mul]
      simp only [mul_assoc]
      rw [hcov n F]
    rw [hrew, CStarRing.norm_mul_coe_unitary]
    refine (P.norm_ι_le _).trans ((norm_mul_mul_le_of_le_one ?_ ?_ _).trans ?_)
    · rw [norm_star]; exact hF1.le
    · exact (NonUnitalStarAlgHom.norm_apply_le (S.shift n) F).trans hF1.le
    · linarith [happ (b n)]

/-- **A Bernoulli shift over a simple coefficient algebra gives a simple crossed product.** -/
theorem isSimpleCStar_of_shiftModel [Nontrivial D] (hC : IsSimpleCStar C) (S : ShiftModel Z C)
    (P : CovariantExpectation C D)
    (hcov : ∀ (n : ℤ) (c : C),
      ((P.u ^ n : unitary D) : D) * P.ι c = P.ι (S.shift n c) * ((P.u ^ n : unitary D) : D))
    {g h : Z} (hg : ‖g‖ = 1) (hh : ‖h‖ = 1) (hhg : star h * g = 0) : IsSimpleCStar D :=
  isSimpleCStar_of_kishimoto hC P (kishimotoCondition_of_shiftModel S P hcov hg hh hhg)

end XCVWitness
end GroupApproximation
