import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Algebraic lemmas for the affine presentation (lane k2-panin)

Three facts used by `PaninAffine.Main`, each stated for general rings.

* **Field extension.** Let `K → L` be a field extension. Relatively prime polynomials in
  `K[s]` stay relatively prime in `L[s]` (`isRelPrime_map_of_isRelPrime`). The proof applies
  `K`-linear functionals `L → K` to the coefficients (`coeffMap`).
* **The blow-up chart.** Let `ψ : κ[s₀..sₙ] → κ[A₁..Aₙ][X]` send `s₀ ↦ X` and `sⱼ₊₁ ↦ X·Aⱼ`
  (`chart`). It is injective, and every element of the target becomes an image after
  multiplying by a power of `X`. So `ψ` keeps `p` and `q` relatively prime whenever `q` has a
  nonzero constant term (`isRelPrime_chart`).
* **Gauss.** Let `R₀` be a GCD domain. Polynomials that are relatively prime in `R₀[X]` are
  coprime over the fraction field (`isCoprime_map_fractionRing_of_isRelPrime`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open MvPolynomial

section CoeffMap

variable {σ K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a `K`-linear functional `ℓ : L → K` to every coefficient of a polynomial over `L`. -/
noncomputable def coeffMap (ℓ : L →ₗ[K] K) (p : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ α ∈ p.support, monomial α (ℓ (p.coeff α))

theorem coeff_coeffMap (ℓ : L →ₗ[K] K) (p : MvPolynomial σ L) (β : σ →₀ ℕ) :
    (coeffMap ℓ p).coeff β = ℓ (p.coeff β) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single β]
  · simp
  · intro α _ hne
    simp [hne]
  · intro hβ
    rw [notMem_support_iff.mp hβ, map_zero]
    simp

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coeff_coeffMap

/-- `coeffMap ℓ` is `K[s]`-linear on polynomials with coefficients from `K`. -/
theorem coeffMap_map_mul (ℓ : L →ₗ[K] K) (f : MvPolynomial σ K) (u : MvPolynomial σ L) :
    coeffMap ℓ (map (algebraMap K L) f * u) = f * coeffMap ℓ u := by
  classical
  ext β
  rw [coeff_coeffMap, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_coeffMap, ← Algebra.smul_def, map_smul, smul_eq_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coeffMap_map_mul

/-- Reconstruction: if `g` divides every `coeffMap ℓ u`, then `g` divides `u` over `L`. -/
theorem map_dvd_of_forall_dvd_coeffMap {g : MvPolynomial σ K} {u : MvPolynomial σ L}
    (h : ∀ ℓ : L →ₗ[K] K, g ∣ coeffMap ℓ u) : map (algebraMap K L) g ∣ u := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  let J := u.support.biUnion fun α => (b.repr (u.coeff α)).support
  have h' : ∀ j, ∃ c, coeffMap (b.coord j) u = g * c := fun j => h (b.coord j)
  choose t ht using h'
  refine ⟨∑ j ∈ J, C (b j) * map (algebraMap K L) (t j), ?_⟩
  rw [Finset.mul_sum]
  have key : ∀ j, map (algebraMap K L) g * (C (b j) * map (algebraMap K L) (t j)) =
      C (b j) * map (algebraMap K L) (coeffMap (b.coord j) u) := by
    intro j
    rw [ht j, map_mul]
    ring
  simp_rw [key]
  ext α
  rw [coeff_sum]
  simp only [coeff_C_mul, coeff_map, coeff_coeffMap]
  have hcoord : ∀ j, b.coord j (u.coeff α) = b.repr (u.coeff α) j := fun _ => rfl
  simp only [hcoord]
  have hsub : (b.repr (u.coeff α)).support ⊆ J := by
    intro j hj
    by_cases hα : α ∈ u.support
    · exact Finset.mem_biUnion.mpr ⟨α, hα, hj⟩
    · rw [notMem_support_iff.mp hα, map_zero] at hj
      simp at hj
  have hrepr : u.coeff α =
      ∑ j ∈ (b.repr (u.coeff α)).support, (b.repr (u.coeff α)) j • b j := by
    conv_lhs => rw [← b.linearCombination_repr (u.coeff α)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_lhs => rw [hrepr]
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  · intro j _ hj
    rw [Finsupp.notMem_support_iff.mp hj, zero_smul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.map_dvd_of_forall_dvd_coeffMap

/-- **Relative primality survives field extension** for multivariate polynomials. -/
theorem isRelPrime_map_of_isRelPrime {f g : MvPolynomial σ K} (h : IsRelPrime f g) :
    IsRelPrime (map (algebraMap K L) f) (map (algebraMap K L) g) := by
  classical
  intro d hdf hdg
  by_cases hg0 : g = 0
  · subst hg0
    have hf : IsUnit f := h dvd_rfl (dvd_zero f)
    exact isUnit_of_dvd_unit hdf (hf.map (MvPolynomial.map (algebraMap K L)))
  obtain ⟨w, hw⟩ := hdf
  obtain ⟨u, hu⟩ := hdg
  have hmul : map (algebraMap K L) f * u = map (algebraMap K L) g * w := by
    rw [hw, hu]
    ring
  have hall : ∀ ℓ : L →ₗ[K] K, g ∣ coeffMap ℓ u := by
    intro ℓ
    have h1 := congrArg (coeffMap ℓ) hmul
    rw [coeffMap_map_mul, coeffMap_map_mul] at h1
    exact h.symm.dvd_of_dvd_mul_left ⟨coeffMap ℓ w, h1⟩
  obtain ⟨v, hv⟩ := map_dvd_of_forall_dvd_coeffMap hall
  have hg' : map (algebraMap K L) g ≠ 0 := fun h0 =>
    hg0 (MvPolynomial.map_injective _ (algebraMap K L).injective (by rw [h0, map_zero]))
  have h2 : map (algebraMap K L) g * 1 = map (algebraMap K L) g * (d * v) := by
    rw [mul_one]
    nth_rw 1 [hu]
    rw [hv]
    ring
  exact IsUnit.of_mul_eq_one v (mul_left_cancel₀ hg' h2).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isRelPrime_map_of_isRelPrime

/-- Some coefficient functional does not kill a nonzero polynomial. -/
theorem exists_coeffMap_ne_zero {P : MvPolynomial σ L} (hP : P ≠ 0) :
    ∃ ℓ : L →ₗ[K] K, coeffMap ℓ P ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hP
  let b := Module.Basis.ofVectorSpace K L
  have hb : b.repr (P.coeff d) ≠ 0 := fun h0 => hd (b.repr.map_eq_zero_iff.mp h0)
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hb
  refine ⟨b.coord j, fun h0 => hj ?_⟩
  have h1 := congrArg (MvPolynomial.coeff d) h0
  rw [coeff_coeffMap, coeff_zero] at h1
  rw [Finsupp.coe_zero, Pi.zero_apply]
  exact h1

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_coeffMap_ne_zero

/-- Evaluation at a `K`-point commutes with `coeffMap`. -/
theorem eval_coeffMap (ℓ : L →ₗ[K] K) (a : σ → K) (P : MvPolynomial σ L) :
    eval a (coeffMap ℓ P) = ℓ (eval (fun j => algebraMap K L (a j)) P) := by
  classical
  rw [coeffMap, map_sum]
  conv_rhs => rw [MvPolynomial.eval_eq, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [eval_monomial, Finsupp.prod]
  have hprod : ∏ i ∈ d.support, algebraMap K L (a i) ^ d i =
      algebraMap K L (∏ i ∈ d.support, a i ^ d i) := by
    rw [map_prod]
    simp only [map_pow]
  rw [hprod, mul_comm (P.coeff d), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.eval_coeffMap

end CoeffMap

section Equiv

/-- Multiplicative equivalences preserve relative primality. -/
theorem isRelPrime_map_mulEquiv {A B : Type*} [CommMonoid A] [CommMonoid B] (e : A ≃* B)
    {a b : A} (h : IsRelPrime a b) : IsRelPrime (e a) (e b) := by
  intro d hda hdb
  have h1 : e.symm d ∣ a := by simpa using map_dvd e.symm hda
  have h2 : e.symm d ∣ b := by simpa using map_dvd e.symm hdb
  simpa using (h h1 h2).map e

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isRelPrime_map_mulEquiv

end Equiv

section Chart

variable {κ : Type*} [Field κ] {n : ℕ}

/-- The exponent map of the blow-up chart: `α ↦ α + (α₁ + ⋯ + αₙ) • e₀`. -/
noncomputable def chartExp (n : ℕ) : (Fin (n + 1) →₀ ℕ) →+ (Fin (n + 1) →₀ ℕ) where
  toFun α := α + (∑ j : Fin n, α j.succ) • Finsupp.single 0 1
  map_zero' := by simp
  map_add' α β := by
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, add_smul]
    abel

theorem chartExp_apply_succ (α : Fin (n + 1) →₀ ℕ) (j : Fin n) :
    chartExp n α j.succ = α j.succ := by
  show ((α + (∑ j : Fin n, α j.succ) • Finsupp.single 0 1 : Fin (n + 1) →₀ ℕ)) j.succ = α j.succ
  rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero j),
    smul_zero, add_zero]

theorem chartExp_apply_zero (α : Fin (n + 1) →₀ ℕ) :
    chartExp n α 0 = α 0 + ∑ j : Fin n, α j.succ := by
  show ((α + (∑ j : Fin n, α j.succ) • Finsupp.single 0 1 : Fin (n + 1) →₀ ℕ)) 0 = _
  rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem chartExp_injective : Function.Injective (chartExp n) := by
  intro α β h
  have hs : ∀ j : Fin n, α j.succ = β j.succ := by
    intro j
    have := DFunLike.congr_fun h j.succ
    rwa [chartExp_apply_succ, chartExp_apply_succ] at this
  ext i
  refine Fin.cases ?_ (fun j => hs j) i
  have h0 := DFunLike.congr_fun h 0
  rw [chartExp_apply_zero, chartExp_apply_zero] at h0
  have hsum : (∑ j : Fin n, α j.succ) = ∑ j : Fin n, β j.succ :=
    Finset.sum_congr rfl fun j _ => hs j
  omega

theorem chartExp_single_zero : chartExp n (Finsupp.single 0 1) = Finsupp.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [chartExp_apply_zero,
      Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne (Fin.succ_ne_zero j), add_zero]
  · rw [chartExp_apply_succ]

theorem chartExp_single_succ (j : Fin n) :
    chartExp n (Finsupp.single j.succ 1) = Finsupp.single j.succ 1 + Finsupp.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [chartExp_apply_zero, Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero j).symm,
      Finsupp.single_eq_same]
    simp [Finsupp.single_apply, Fin.succ_inj]
  · rw [chartExp_apply_succ, Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero k),
      add_zero]

/-- The blow-up chart on exponents, as a ring map `κ[s] → κ[s]` (`s₀ ↦ s₀`, `sⱼ₊₁ ↦ s₀ sⱼ₊₁`). -/
noncomputable def chartMono (n : ℕ) : MvPolynomial (Fin (n + 1)) κ →+* MvPolynomial (Fin (n + 1)) κ :=
  AddMonoidAlgebra.mapDomainRingHom κ (chartExp n)

theorem chartMono_monomial (α : Fin (n + 1) →₀ ℕ) (c : κ) :
    chartMono n (monomial α c) = monomial (chartExp n α) c := by
  rw [chartMono, AddMonoidAlgebra.mapDomainRingHom_apply, ← single_eq_monomial,
    ← single_eq_monomial, AddMonoidAlgebra.mapDomain_single]

theorem chartMono_injective : Function.Injective (chartMono (κ := κ) n) := by
  intro p q h
  exact AddMonoidAlgebra.mapDomain_injective chartExp_injective h

theorem chartMono_C (c : κ) : chartMono n (C c) = C c := by
  rw [C_apply, chartMono_monomial, map_zero]

theorem chartMono_X_zero : chartMono (κ := κ) n (X 0) = X 0 := by
  have h := chartMono_monomial (κ := κ) (n := n) (Finsupp.single 0 1) 1
  rw [chartExp_single_zero] at h
  exact h

theorem chartMono_X_succ (j : Fin n) : chartMono (κ := κ) n (X j.succ) = X j.succ * X 0 := by
  have h := chartMono_monomial (κ := κ) (n := n) (Finsupp.single j.succ 1) 1
  rw [chartExp_single_succ] at h
  rw [show (X j.succ * X 0 : MvPolynomial (Fin (n + 1)) κ) =
      monomial (Finsupp.single j.succ 1 + Finsupp.single 0 1) 1 by
    simp only [MvPolynomial.X, monomial_mul, mul_one]]
  exact h

theorem finSuccEquiv_C' {R : Type*} [CommSemiring R] (c : R) :
    finSuccEquiv R n (C c) = Polynomial.C (C c) := by
  simp [finSuccEquiv_apply]

/-- **The blow-up chart** `κ[s₀..sₙ] → κ[A₁..Aₙ][X]`: `s₀ ↦ X`, `sⱼ₊₁ ↦ X·Aⱼ`. -/
noncomputable def chart (κ : Type*) [Field κ] (n : ℕ) :
    MvPolynomial (Fin (n + 1)) κ →ₐ[κ] Polynomial (MvPolynomial (Fin n) κ) :=
  aeval (Fin.cons Polynomial.X fun j => Polynomial.X * Polynomial.C (X j))

theorem chart_X_zero : chart κ n (X 0) = Polynomial.X := by
  simp [chart]

theorem chart_X_succ (j : Fin n) : chart κ n (X j.succ) = Polynomial.X * Polynomial.C (X j) := by
  simp [chart]

theorem chart_C (c : κ) : chart κ n (C c) = Polynomial.C (C c) := by
  simp [chart, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem chart_apply (p : MvPolynomial (Fin (n + 1)) κ) :
    chart κ n p = finSuccEquiv κ n (chartMono n p) := by
  have hX : ∀ i, chart κ n (X i) = finSuccEquiv κ n (chartMono n (X i)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [chart_X_zero, chartMono_X_zero, finSuccEquiv_X_zero]
    · rw [chart_X_succ, chartMono_X_succ, map_mul, finSuccEquiv_X_succ, finSuccEquiv_X_zero,
        mul_comm]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [chart_C, chartMono_C, finSuccEquiv_C']
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, hX]

theorem chart_injective : Function.Injective (chart κ n) := by
  intro p q h
  rw [chart_apply, chart_apply] at h
  exact chartMono_injective ((finSuccEquiv κ n).injective h)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.chart_injective

/-- The constant coefficient (in `X`) of `ψ q` is the constant term of `q`. -/
theorem chart_coeff_zero (q : MvPolynomial (Fin (n + 1)) κ) :
    (chart κ n q).coeff 0 = C (constantCoeff q) := by
  have hX : ∀ i, (chart κ n (X i)).coeff 0 = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [chart_X_zero, Polynomial.coeff_X_zero]
    · rw [chart_X_succ, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul]
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [chart_C, Polynomial.coeff_C_zero, constantCoeff_C]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.mul_coeff_zero, hp, hX, mul_zero, constantCoeff_X, map_zero]

/-- Every element of `κ[A][X]` times a power of `X` lies in the image of the chart. -/
theorem exists_X_pow_mul_eq_chart (r : Polynomial (MvPolynomial (Fin n) κ)) :
    ∃ (m : ℕ) (D : MvPolynomial (Fin (n + 1)) κ), Polynomial.X ^ m * r = chart κ n D := by
  have hC : ∀ a : MvPolynomial (Fin n) κ, ∃ (m : ℕ) (D : MvPolynomial (Fin (n + 1)) κ),
      Polynomial.X ^ m * Polynomial.C a = chart κ n D := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      exact ⟨0, C c, by rw [pow_zero, one_mul, chart_C]⟩
    | add a b ha hb =>
      obtain ⟨m, D, hD⟩ := ha
      obtain ⟨m', D', hD'⟩ := hb
      refine ⟨m + m', X 0 ^ m' * D + X 0 ^ m * D', ?_⟩
      have e : chart κ n (X 0 ^ m' * D + X 0 ^ m * D') =
          Polynomial.X ^ m' * chart κ n D + Polynomial.X ^ m * chart κ n D' := by
        simp [chart_X_zero]
      rw [e, ← hD, ← hD', Polynomial.C_add]
      ring
    | mul_X a j ha =>
      obtain ⟨m, D, hD⟩ := ha
      refine ⟨m + 1, D * X j.succ, ?_⟩
      rw [show chart κ n (D * X j.succ) = chart κ n D * (Polynomial.X * Polynomial.C (X j)) by
        rw [map_mul, chart_X_succ], ← hD, Polynomial.C_mul]
      ring
  refine Polynomial.induction_on' r ?_ ?_
  · rintro p q ⟨m, D, hD⟩ ⟨m', D', hD'⟩
    refine ⟨m + m', X 0 ^ m' * D + X 0 ^ m * D', ?_⟩
    have e : chart κ n (X 0 ^ m' * D + X 0 ^ m * D') =
        Polynomial.X ^ m' * chart κ n D + Polynomial.X ^ m * chart κ n D' := by
      simp [chart_X_zero]
    rw [e, ← hD, ← hD']
    ring
  · intro k a
    obtain ⟨m, D, hD⟩ := hC a
    refine ⟨m, D * X 0 ^ k, ?_⟩
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, chart_X_zero, ← hD]
    ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_X_pow_mul_eq_chart

/-- **The chart keeps polynomials relatively prime**, provided the second has a nonzero
constant term. -/
theorem isRelPrime_chart {p q : MvPolynomial (Fin (n + 1)) κ} (h : IsRelPrime p q)
    (hq : constantCoeff q ≠ 0) : IsRelPrime (chart κ n p) (chart κ n q) := by
  intro d hdp hdq
  have hcoeff : (chart κ n q).coeff 0 = C (constantCoeff q) := chart_coeff_zero q
  have hXq : ¬ (Polynomial.X ∣ chart κ n q) := by
    rw [Polynomial.X_dvd_iff, hcoeff]
    exact fun h0 => hq (MvPolynomial.C_eq_zero.mp h0)
  have hq0 : chart κ n q ≠ 0 := fun h0 => hXq (by rw [h0]; exact dvd_zero _)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hq0 (zero_dvd_iff.mp hdq)
  have hXd : ¬ (Polynomial.X ∣ d) := fun h' => hXq (h'.trans hdq)
  obtain ⟨m, D, hD⟩ := exists_X_pow_mul_eq_chart d
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD
    exact hd0 ((mul_eq_zero.mp hD).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero))
  have key : ∀ {g : MvPolynomial (Fin (n + 1)) κ}, d ∣ chart κ n g → ∃ N, D ∣ X 0 ^ N * g := by
    intro g hg
    obtain ⟨r, hr⟩ := hg
    obtain ⟨m₁, R₁, hR₁⟩ := exists_X_pow_mul_eq_chart r
    refine ⟨m + m₁, R₁, ?_⟩
    apply chart_injective
    rw [map_mul, map_mul, map_pow, chart_X_zero, ← hD, ← hR₁, hr]
    ring
  obtain ⟨N₁, hp'⟩ := key hdp
  obtain ⟨N₂, hq'⟩ := key hdq
  have hX0 : Prime (X 0 : MvPolynomial (Fin (n + 1)) κ) := MvPolynomial.X_prime (i := 0)
  obtain ⟨e, D₀, hD₀, hDe⟩ := WfDvdMonoid.max_power_factor hD0 hX0.irreducible
  have hcop : ∀ N, IsRelPrime D₀ (X 0 ^ N) := fun N =>
    ((hX0.irreducible.isRelPrime_iff_not_dvd).mpr hD₀).symm.pow_right
  have hD₀D : D₀ ∣ D := ⟨X 0 ^ e, by rw [hDe, mul_comm]⟩
  have hD₀p : D₀ ∣ p := (hcop N₁).dvd_of_dvd_mul_left (hD₀D.trans hp')
  have hD₀q : D₀ ∣ q := (hcop N₂).dvd_of_dvd_mul_left (hD₀D.trans hq')
  have hu : IsUnit D₀ := h hD₀p hD₀q
  have hu' : IsUnit (chart κ n D₀) := hu.map _
  have hXmd : Polynomial.X ^ m * d = Polynomial.X ^ e * chart κ n D₀ := by
    rw [hD, hDe, map_mul, map_pow, chart_X_zero]
  rcases le_or_gt m e with hme | hem
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hme
    have h2 : d = Polynomial.X ^ k * chart κ n D₀ := by
      apply mul_left_cancel₀ (pow_ne_zero m (Polynomial.X_ne_zero (R := MvPolynomial (Fin n) κ)))
      rw [hXmd, pow_add, mul_assoc]
    rcases k with _ | k
    · rw [pow_zero, one_mul] at h2
      rw [h2]
      exact hu'
    · exact absurd (by rw [h2]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero k)) _)
        hXd
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hem
    have h2 : Polynomial.X ^ (k + 1) * d = chart κ n D₀ := by
      apply mul_left_cancel₀ (pow_ne_zero e (Polynomial.X_ne_zero (R := MvPolynomial (Fin n) κ)))
      rw [← hXmd, hk]
      ring
    have hXu : IsUnit (Polynomial.X : Polynomial (MvPolynomial (Fin n) κ)) :=
      isUnit_of_dvd_unit ((dvd_mul_of_dvd_left (dvd_pow_self Polynomial.X (Nat.succ_ne_zero k)) d).trans
        ⟨1, by rw [mul_one]; exact h2.symm⟩) hu'
    exact absurd hXu Polynomial.not_isUnit_X

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isRelPrime_chart

end Chart

section Gauss

/-- **Gauss.** Relatively prime polynomials over a GCD domain are coprime over its fraction
field. -/
theorem isCoprime_map_fractionRing_of_isRelPrime {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    [IsGCDMonoid R₀] {P Q : Polynomial R₀} (h : IsRelPrime P Q) (hQ : Q ≠ 0) :
    IsCoprime (P.map (algebraMap R₀ (FractionRing R₀)))
      (Q.map (algebraMap R₀ (FractionRing R₀))) := by
  classical
  let : NormalizedGCDMonoid R₀ := Nonempty.some inferInstance
  have hinj : Function.Injective (algebraMap R₀ (FractionRing R₀)) :=
    IsFractionRing.injective R₀ (FractionRing R₀)
  rw [← isRelPrime_iff_isCoprime]
  intro g hgP hgQ
  have hQF : Q.map (algebraMap R₀ (FractionRing R₀)) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hQ
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hQF (zero_dvd_iff.mp hgQ)
  obtain ⟨b, hb, hbg⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R₀) g
  rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hbg
  have hb0 : algebraMap R₀ (FractionRing R₀) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hdvd : ∀ {H : Polynomial R₀}, g ∣ H.map (algebraMap R₀ (FractionRing R₀)) →
      (IsLocalization.integerNormalization (nonZeroDivisors R₀) g).primPart ∣ H := by
    intro H hH
    refine (Polynomial.isPrimitive_primPart _).dvd_of_fraction_map_dvd_fraction_map
      (K := FractionRing R₀) ?_
    have h1 := Polynomial.map_dvd (algebraMap R₀ (FractionRing R₀))
      (Polynomial.primPart_dvd (IsLocalization.integerNormalization (nonZeroDivisors R₀) g))
    rw [hbg] at h1
    have h2 := h1.trans (mul_dvd_mul_left
      (Polynomial.C (algebraMap R₀ (FractionRing R₀) b)) hH)
    exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb0))).mp h2
  have hu := h (hdvd hgP) (hdvd hgQ)
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hg0 hu

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isCoprime_map_fractionRing_of_isRelPrime

/-- A Bézout identity with a nonzero constant makes two polynomials over a field coprime. -/
theorem isCoprime_of_eq_C {κ : Type*} [Field κ] {f g p q : Polynomial κ} {c : κ}
    (h : f * p + g * q = Polynomial.C c) (hc : c ≠ 0) : IsCoprime f g := by
  refine ⟨Polynomial.C c⁻¹ * p, Polynomial.C c⁻¹ * q, ?_⟩
  have hc' : Polynomial.C c⁻¹ * Polynomial.C c = (1 : Polynomial κ) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]
  linear_combination (Polynomial.C c⁻¹) * h + hc'

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isCoprime_of_eq_C

end Gauss

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
