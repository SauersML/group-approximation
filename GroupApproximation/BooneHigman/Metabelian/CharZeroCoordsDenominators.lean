import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Prod
import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Clearing denominators in polynomial matrix coordinates (lane bh-met-30)

Research node `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`, last step of the
route of `CharZeroHost.FGSubringCoordinatesStatement`:

  "The images of the finitely many generators of `B` have entries with finitely many
  denominators, with product `m`; the matrices with entries in `ℤ[1/m][x'] ⊆ ℚ[x']` form a
  subring containing them, so the embedding of `B` lands in `M(ℤ[1/m][x'])`."

**Route.**
* `away_ringHom_injective`: every ring homomorphism `ℤ[1/m] → ℚ` is injective (write
  `z · m^n = a`; `a ↦ 0` forces `a = 0`).
* `rat_mem_range_of_den_dvd`: if `den q ∣ m ≠ 0` then `q = (num q · c) · m⁻¹` lies in the image.
* `mvPolynomial_mem_range_of_den_dvd`, `matrix_mem_range_mapMatrix`: coefficientwise, then
  entrywise (`MvPolynomial.mem_range_map_iff_coeffs_subset`).
* `exists_den_dvd`: a finite family of rational polynomials has a common denominator.
* `exists_matrixEmbedding_away_of_closure`: for `F : closure t ↪ M_N(ℚ[x])`, take `m` a common
  denominator of the entries of the `F`-images of the generators; the preimage under `F` of the
  subring `M_N(ℤ[1/m][x]) ⊆ M_N(ℚ[x])` contains the generators (`Subring.closure_le`), hence is
  everything, so `F` corestricts to an injective ring homomorphism into `M_N(ℤ[1/m][x])`.
-/

open GroupApproximation.BooneHigman.Coordinates

namespace GroupApproximation.BooneHigman.Metabelian.CharZeroHost

/-- Every ring homomorphism `ℤ[1/m] → ℚ` is injective. -/
theorem away_ringHom_injective {m : ℕ} (θ : Localization.Away (m : ℤ) →+* ℚ) :
    Function.Injective θ := by
  refine (injective_iff_map_eq_zero θ).2 fun z hz => ?_
  obtain ⟨x, hs⟩ := IsLocalization.surj (Submonoid.powers (m : ℤ)) z
  have hu : IsUnit (algebraMap ℤ (Localization.Away (m : ℤ)) x.2) :=
    IsLocalization.map_units (Localization.Away (m : ℤ)) x.2
  have h1 : ((x.1 : ℤ) : ℚ) = 0 := by
    have h := congrArg θ hs
    rw [map_mul, hz, zero_mul, eq_intCast (algebraMap ℤ (Localization.Away (m : ℤ))) x.1,
      map_intCast] at h
    exact h.symm
  rw [Int.cast_eq_zero.1 h1, map_zero] at hs
  exact hu.mul_left_eq_zero.1 hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.away_ringHom_injective

/-- A rational number whose denominator divides `m ≠ 0` lies in the image of `ℤ[1/m] → ℚ`. -/
theorem rat_mem_range_of_den_dvd {m : ℕ} (hm : m ≠ 0) (θ : Localization.Away (m : ℤ) →+* ℚ)
    {q : ℚ} (hq : q.den ∣ m) : q ∈ θ.range := by
  have hu : IsUnit (algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ)) :=
    IsLocalization.map_units (Localization.Away (m : ℤ))
      (⟨(m : ℤ), Submonoid.mem_powers (m : ℤ)⟩ : Submonoid.powers (m : ℤ))
  have hθm : θ (algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ)) = (m : ℚ) := by
    rw [eq_intCast (algebraMap ℤ (Localization.Away (m : ℤ))) (m : ℤ), map_intCast,
      Int.cast_natCast]
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have h1 : θ ↑hu.unit⁻¹ * (m : ℚ) = 1 := by
    rw [← hθm, ← map_mul, hu.val_inv_mul, map_one]
  have hθinv : θ ↑hu.unit⁻¹ = (m : ℚ)⁻¹ :=
    calc θ ↑hu.unit⁻¹ = θ ↑hu.unit⁻¹ * (m : ℚ) * (m : ℚ)⁻¹ :=
          (mul_inv_cancel_right₀ hm0 _).symm
      _ = (m : ℚ)⁻¹ := by rw [h1, one_mul]
  obtain ⟨c, hc⟩ := hq
  refine RingHom.mem_range.2
    ⟨((q.num * (c : ℤ) : ℤ) : Localization.Away (m : ℤ)) * ↑hu.unit⁻¹, ?_⟩
  rw [map_mul, map_intCast, hθinv, Int.cast_mul, Int.cast_natCast, ← Rat.mul_den_eq_num,
    mul_assoc q (q.den : ℚ) (c : ℚ), ← Nat.cast_mul, ← hc, mul_inv_cancel_right₀ hm0]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.rat_mem_range_of_den_dvd

/-- A rational polynomial all of whose coefficients have denominator dividing `m ≠ 0` has
coefficients in `ℤ[1/m]`. -/
theorem mvPolynomial_mem_range_of_den_dvd {σ : Type*} {m : ℕ} (hm : m ≠ 0)
    (θ : Localization.Away (m : ℤ) →+* ℚ) {p : MvPolynomial σ ℚ}
    (hp : ∀ c ∈ p.coeffs, c.den ∣ m) : p ∈ (MvPolynomial.map (σ := σ) θ).range := by
  obtain ⟨p', hp'⟩ := (MvPolynomial.mem_range_map_iff_coeffs_subset (f := θ) (x := p)).2
    fun c hc => RingHom.mem_range.1 (rat_mem_range_of_den_dvd hm θ (hp c (Finset.mem_coe.1 hc)))
  exact RingHom.mem_range.2 ⟨p', hp'⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mvPolynomial_mem_range_of_den_dvd

/-- A matrix all of whose entries lie in the range of `f` lies in the range of `f.mapMatrix`. -/
theorem matrix_mem_range_mapMatrix {α β : Type*} [Ring α] [Ring β] {N : ℕ} (f : α →+* β)
    {M : Matrix (Fin N) (Fin N) β} (hM : ∀ i j, M i j ∈ f.range) :
    M ∈ (f.mapMatrix : Matrix (Fin N) (Fin N) α →+* Matrix (Fin N) (Fin N) β).range := by
  choose M' hM' using fun i j => RingHom.mem_range.1 (hM i j)
  exact RingHom.mem_range.2 ⟨M', Matrix.ext fun i j => by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hM' i j⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.matrix_mem_range_mapMatrix

/-- A finite family of rational polynomials has a common denominator. -/
theorem exists_den_dvd {ι σ : Type*} [Fintype ι] (F : ι → MvPolynomial σ ℚ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ e, ∀ c ∈ (F e).coeffs, c.den ∣ m := by
  refine ⟨∏ e, ∏ c ∈ (F e).coeffs, c.den, ?_, fun e c hc => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun _ _ =>
      Finset.prod_ne_zero_iff.2 fun c _ => Rat.den_ne_zero c
  · exact (Finset.dvd_prod_of_mem (fun c : ℚ => c.den) hc).trans
      (Finset.dvd_prod_of_mem (fun e => ∏ c ∈ (F e).coeffs, c.den) (Finset.mem_univ e))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_den_dvd

/-- **Clearing denominators.**  If the subring `ℤ[t]` generated by a finite set `t` embeds in
`M_N(ℚ[x_0, …, x_{s-1}])`, then it embeds in `M_N(ℤ[1/m][x_0, …, x_{s-1}])` for some `m`. -/
theorem exists_matrixEmbedding_away_of_closure {K : Type*} [Ring K] (t : Finset K) {s N : ℕ}
    (F : Subring.closure (↑t : Set K) →+* Matrix (Fin N) (Fin N) (MvPolynomial (Fin s) ℚ))
    (hF : Function.Injective F) :
    ∃ m : ℕ, MatrixEmbedding (Subring.closure (↑t : Set K))
      (MvPolynomial (Fin s) (Localization.Away (m : ℤ))) := by
  obtain ⟨m, hm, hden⟩ := exists_den_dvd
    (fun e : (↥t × Fin N × Fin N) =>
      F ⟨e.1.1, Subring.subset_closure (Finset.mem_coe.2 e.1.2)⟩ e.2.1 e.2.2)
  have hu : IsUnit (Int.castRingHom ℚ (m : ℤ)) := by
    rw [eq_intCast (Int.castRingHom ℚ) (m : ℤ), Int.cast_natCast]
    exact Ne.isUnit (Nat.cast_ne_zero.2 hm)
  let θ : Localization.Away (m : ℤ) →+* ℚ := IsLocalization.Away.lift (m : ℤ) hu
  let Θ : Matrix (Fin N) (Fin N) (MvPolynomial (Fin s) (Localization.Away (m : ℤ))) →+*
      Matrix (Fin N) (Fin N) (MvPolynomial (Fin s) ℚ) := (MvPolynomial.map (σ := Fin s) θ).mapMatrix
  have hΘ : Function.Injective Θ :=
    Matrix.map_injective (MvPolynomial.map_injective θ (away_ringHom_injective θ))
  have hgen : ∀ x (hx : x ∈ (↑t : Set K)), F ⟨x, Subring.subset_closure hx⟩ ∈ Θ.range :=
    fun x hx => matrix_mem_range_mapMatrix (MvPolynomial.map (σ := Fin s) θ) fun i j =>
      mvPolynomial_mem_range_of_den_dvd hm θ (hden (⟨x, Finset.mem_coe.1 hx⟩, i, j))
  have hT : Subring.closure (↑t : Set K) ≤
      Subring.map (Subring.closure (↑t : Set K)).subtype (Subring.comap F Θ.range) := by
    rw [Subring.closure_le]
    intro x hx
    exact Subring.mem_map.2
      ⟨⟨x, Subring.subset_closure hx⟩, Subring.mem_comap.2 (hgen x hx), rfl⟩
  have hall : ∀ b, F b ∈ Θ.range := fun b => by
    obtain ⟨b', hb', hbb'⟩ := Subring.mem_map.1 (hT b.2)
    have hb : b' = b := Subtype.ext hbb'
    rw [← hb]
    exact Subring.mem_comap.1 hb'
  let e := RingEquiv.ofBijective Θ.rangeRestrict
    ⟨fun _ _ h => hΘ (congrArg Subtype.val h), Θ.rangeRestrict_surjective⟩
  have hcod : Function.Injective (F.codRestrict Θ.range hall) :=
    fun _ _ h => hF (congrArg Subtype.val h)
  exact ⟨m, N, e.symm.toRingHom.comp (F.codRestrict Θ.range hall), e.symm.injective.comp hcod⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_matrixEmbedding_away_of_closure

end GroupApproximation.BooneHigman.Metabelian.CharZeroHost
