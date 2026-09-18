import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.UpperTriangular
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.CoarseTransfer
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Property A from a dyadic grid approximation

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: the Guentner--Higson--Weinberger step for
`Σ ≤ GL₄(ℚ)`.  If every element `γ` of an integral subgroup `Γ` lies within
bounded distance (bounded entries of `b⁻¹ γ` and `γ⁻¹ b`) of a dyadic grid
point `b = diag(2^k) · m` of the Borel subgroup, then `γ ↦ b γ` is a
finite-scale coarse embedding of `Γ` into `borel`
(`CoarseTransfer.hasPropertyA_of_coarse`):

* **bornology**: `(b g)⁻¹ b (g r)` has bounded entries in both directions, and
  bounded grid quotients are dyadic with bounded denominators
  (`isIntegral_pow_smul_gridQuotient`), hence range over a finite set;
* **properness**: `g⁻¹ h = (g⁻¹ b g)((b g)⁻¹ b h)((b h)⁻¹ h)` has bounded
  integral entries, hence ranges over a finite set.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel GroupApproximation.ExactnessPermanence

/-- Factorisation of a quotient through two intermediate points. -/
theorem factor_three {G : Type*} [Group G] (p q s t : G) :
    p⁻¹ * t = (p⁻¹ * q) * (q⁻¹ * s) * (s⁻¹ * t) := by
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Entry bound for a product of `4 × 4` matrices. -/
theorem abs_mul_apply_le {a b : Mat} {A B : ℚ} (ha : ∀ i j, |a i j| ≤ A)
    (hb : ∀ i j, |b i j| ≤ B) (i j : Fin 4) : |(a * b) i j| ≤ 4 * (A * B) := by
  rw [Matrix.mul_apply]
  calc |∑ k, a i k * b k j| ≤ ∑ k, |a i k * b k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 4, A * B := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact mul_le_mul (ha i k) (hb k j) (abs_nonneg _) ((abs_nonneg _).trans (ha i k))
    _ = 4 * (A * B) := by
        rw [Fin.sum_univ_four]
        ring

/-- Entry bound for a triple product. -/
theorem abs_mul3_apply_le {a b d : Mat} {A B D : ℚ} (ha : ∀ i j, |a i j| ≤ A)
    (hb : ∀ i j, |b i j| ≤ B) (hd : ∀ i j, |d i j| ≤ D) (i j : Fin 4) :
    |(a * b * d) i j| ≤ 4 * (4 * (A * B) * D) :=
  abs_mul_apply_le (abs_mul_apply_le ha hb) hd i j

/-- A finite family of matrices has uniformly bounded entries. -/
theorem exists_entry_bound {α : Type*} (S : Finset α) (φ : α → Mat) :
    ∃ M : ℚ, ∀ x ∈ S, ∀ i j, |φ x i j| ≤ M := by
  refine ⟨∑ x ∈ S, ∑ i, ∑ j, |φ x i j|, fun x hx i j ↦ ?_⟩
  calc |φ x i j| ≤ ∑ j', |φ x i j'| :=
        Finset.single_le_sum (f := fun j' ↦ |φ x i j'|) (fun _ _ ↦ abs_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |φ x i' j'| :=
        Finset.single_le_sum (f := fun i' ↦ ∑ j', |φ x i' j'|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ x' ∈ S, ∑ i', ∑ j', |φ x' i' j'| :=
        Finset.single_le_sum (f := fun x' ↦ ∑ i', ∑ j', |φ x' i' j'|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hx

/-- Bounded rationals with denominator dividing `2^E`. -/
def dyadicBall (E : ℕ) (K : ℚ) : Set ℚ :=
  {q | |q| ≤ K ∧ (2 : ℚ) ^ E * q ∈ (Int.castRingHom ℚ).range}

/-- There are finitely many bounded rationals with denominator dividing `2^E`. -/
theorem finite_dyadicBall (E : ℕ) (K : ℚ) : (dyadicBall E K).Finite := by
  have hpos : (0 : ℚ) < 2 ^ E := pow_pos two_pos E
  refine ((Finset.Icc (-⌈K * 2 ^ E⌉) ⌈K * 2 ^ E⌉).finite_toSet.image
    (fun z : ℤ ↦ (z : ℚ) / 2 ^ E)).subset ?_
  rintro q ⟨hq, hmem⟩
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp hmem
  have hz' : (z : ℚ) = 2 ^ E * q := hz
  obtain ⟨hq1, hq2⟩ := abs_le.mp hq
  have hc := Int.le_ceil (K * 2 ^ E)
  have h1 : (2 : ℚ) ^ E * q ≤ 2 ^ E * K := mul_le_mul_of_nonneg_left hq2 hpos.le
  have h2 : (2 : ℚ) ^ E * (-K) ≤ 2 ^ E * q := mul_le_mul_of_nonneg_left hq1 hpos.le
  refine ⟨z, Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨?_, ?_⟩), ?_⟩
  · have hlow : -((⌈K * 2 ^ E⌉ : ℤ) : ℚ) ≤ (z : ℚ) := by linarith
    exact_mod_cast hlow
  · have hup : (z : ℚ) ≤ ((⌈K * 2 ^ E⌉ : ℤ) : ℚ) := by linarith
    exact_mod_cast hup
  · show (z : ℚ) / 2 ^ E = q
    rw [hz', mul_div_cancel_left₀ q hpos.ne']

/-- Matrices with bounded entries and denominators dividing `2^E`. -/
def boundedDyadicMat (E : ℕ) (K : ℚ) : Set Mat :=
  {x | ∀ i j, |x i j| ≤ K ∧ (2 : ℚ) ^ E * x i j ∈ (Int.castRingHom ℚ).range}

theorem mem_boundedDyadicMat {E : ℕ} {K : ℚ} {x : Mat} :
    x ∈ boundedDyadicMat E K ↔
      ∀ i j, |x i j| ≤ K ∧ (2 : ℚ) ^ E * x i j ∈ (Int.castRingHom ℚ).range :=
  Iff.rfl

theorem finite_boundedDyadicMat (E : ℕ) (K : ℚ) : (boundedDyadicMat E K).Finite := by
  have hrow : (Set.pi Set.univ fun _ : Fin 4 ↦ dyadicBall E K).Finite :=
    Set.Finite.pi fun _ ↦ finite_dyadicBall E K
  have hall : (Set.pi Set.univ fun _ : Fin 4 ↦
      Set.pi Set.univ fun _ : Fin 4 ↦ dyadicBall E K).Finite :=
    Set.Finite.pi fun _ ↦ hrow
  refine hall.subset ?_
  intro x hx
  refine Set.mem_univ_pi.mpr fun i ↦ Set.mem_univ_pi.mpr fun j ↦ ?_
  exact mem_boundedDyadicMat.mp hx i j

/-- A subgroup of `GL₄(ℚ)` has finitely many elements in a bounded dyadic box. -/
theorem finite_subgroup_bounded (H : Subgroup Matˣ) (E : ℕ) (K : ℚ) :
    {g : H | ((g : Matˣ) : Mat) ∈ boundedDyadicMat E K}.Finite := by
  have hinj : Set.InjOn (fun g : H ↦ ((g : Matˣ) : Mat))
      ((fun g : H ↦ ((g : Matˣ) : Mat)) ⁻¹' boundedDyadicMat E K) :=
    fun y _ y' _ h ↦ Subtype.ext (Units.ext h)
  exact Set.Finite.preimage hinj (finite_boundedDyadicMat E K)

/-- A grid quotient bounded in both directions lies in a bounded dyadic box. -/
theorem gridQuotient_mem_bounded {p t : Matˣ} (hp : IsGridPoint p) (ht : IsGridPoint t)
    {K : ℚ} {E : ℕ} (hKE : K ≤ 2 ^ E)
    (h1 : ∀ i j, |((p⁻¹ * t : Matˣ) : Mat) i j| ≤ K)
    (h2 : ∀ i j, |((t⁻¹ * p : Matˣ) : Mat) i j| ≤ K) :
    ((p⁻¹ * t : Matˣ) : Mat) ∈ boundedDyadicMat E K := by
  have hint := isIntegral_pow_smul_gridQuotient hp ht E fun l ↦
    ((abs_le.mp (h2 l l)).2).trans hKE
  exact mem_boundedDyadicMat.mpr fun i j ↦ ⟨h1 i j, hint i j⟩

/-- **Guentner--Higson--Weinberger coarse step.**  An integral subgroup of
`GL₄(ℚ)` that is uniformly close to dyadic grid points of the Borel subgroup
has property A as soon as the Borel subgroup does.
`non_mf_group_notes.tex`, `\paragraph{Exactness.}`. -/
theorem hasPropertyA_of_gridApprox (Γ : Subgroup Matˣ) (hint : ∀ γ ∈ Γ, IsIntegralUnit γ)
    (c : ℚ) (b : Matˣ → Matˣ) (hb : ∀ γ, IsGridPoint (b γ))
    (hc : ∀ γ i j, |(((b γ)⁻¹ * γ : Matˣ) : Mat) i j| ≤ c ∧
      |((γ⁻¹ * b γ : Matˣ) : Mat) i j| ≤ c)
    (hD : HasPropertyA borel) : HasPropertyA Γ := by
  refine hasPropertyA_of_coarse (fun g : Γ ↦ (⟨b g, (hb g).mem_borel⟩ : borel)) ?_ ?_ hD
  · intro R
    obtain ⟨M, hM⟩ := exists_entry_bound R fun r ↦ ((r : Matˣ) : Mat)
    obtain ⟨M', hM'⟩ := exists_entry_bound R fun r ↦ (((r : Matˣ)⁻¹ : Matˣ) : Mat)
    obtain ⟨E, hE⟩ := pow_unbounded_of_one_lt (4 * (4 * (c * max M M') * c))
      (one_lt_two : (1 : ℚ) < 2)
    refine ⟨(finite_subgroup_bounded borel E (4 * (4 * (c * max M M') * c))).toFinset, ?_⟩
    intro g r hr
    refine (Set.Finite.mem_toFinset _).mpr ?_
    show (((b g)⁻¹ * b ((g : Matˣ) * r) : Matˣ) : Mat) ∈ boundedDyadicMat E _
    have hr1 : ∀ i j, |((r : Matˣ) : Mat) i j| ≤ max M M' :=
      fun i j ↦ (hM r hr i j).trans (le_max_left _ _)
    have hr2 : ∀ i j, |(((r : Matˣ)⁻¹ : Matˣ) : Mat) i j| ≤ max M M' :=
      fun i j ↦ (hM' r hr i j).trans (le_max_right _ _)
    refine gridQuotient_mem_bounded (hb g) (hb ((g : Matˣ) * r)) hE.le ?_ ?_
    · intro i j
      rw [factor_three (b g) (g : Matˣ) ((g : Matˣ) * r) (b ((g : Matˣ) * r)),
        inv_mul_cancel_left (g : Matˣ) (r : Matˣ), Units.val_mul, Units.val_mul]
      exact abs_mul3_apply_le (fun i j ↦ (hc g i j).1) hr1
        (fun i j ↦ (hc ((g : Matˣ) * r) i j).2) i j
    · intro i j
      have hmid : ((g : Matˣ) * r)⁻¹ * (g : Matˣ) = (r : Matˣ)⁻¹ := by
        rw [mul_inv_rev, inv_mul_cancel_right]
      rw [factor_three (b ((g : Matˣ) * r)) ((g : Matˣ) * r) (g : Matˣ) (b g), hmid,
        Units.val_mul, Units.val_mul]
      exact abs_mul3_apply_le (fun i j ↦ (hc ((g : Matˣ) * r) i j).1) hr2
        (fun i j ↦ (hc g i j).2) i j
  · intro C
    obtain ⟨M, hM⟩ := exists_entry_bound C fun x ↦ ((x : Matˣ) : Mat)
    refine ⟨(finite_subgroup_bounded Γ 0 (4 * (4 * (c * M) * c))).toFinset, ?_⟩
    intro g h hgh
    refine (Set.Finite.mem_toFinset _).mpr ?_
    show (((g : Matˣ)⁻¹ * h : Matˣ) : Mat) ∈ boundedDyadicMat 0 _
    have hC : ∀ i j, |(((b g)⁻¹ * b h : Matˣ) : Mat) i j| ≤ M := hM _ hgh
    refine mem_boundedDyadicMat.mpr fun i j ↦ ⟨?_, ?_⟩
    · rw [factor_three (g : Matˣ) (b g) (b h) (h : Matˣ), Units.val_mul, Units.val_mul]
      exact abs_mul3_apply_le (fun i j ↦ (hc g i j).2) hC
        (fun i j ↦ (hc h i j).1) i j
    · rw [pow_zero, one_mul]
      exact (hint _ (g⁻¹ * h).2).1 i j

end GroupApproximation.Full.NN09b
