import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Hom

/-!
# Laurent-polynomial facts for H.L1

`R = A[T, T⁻¹]`, `𝔄 ⊆ A` an ideal, `B = A[T⁻¹] + 𝔄[T]` (`Graded.horrB 𝔄`).

* `coeffIdeal 𝔄 = 𝔄R`: the Laurent polynomials with all coefficients in `𝔄` (`mem_coeffIdeal`).
* `coeffIdeal_le_horrB`: `𝔄R ⊆ B`.
* `T_neg_mem`: `T⁻ᵏ ∈ B` for `k ≥ 0`.
* `exists_T_neg_mul_mem`: for every `f ∈ R` there is `j` with `T⁻ʲ' f ∈ B` for all `j' ≥ j`; the
  version for columns is `exists_T_neg_smul_mem`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open LaurentPolynomial

variable {A : Type} [CommRing A] (𝔄 : Ideal A)

/-- `𝔄R`: the Laurent polynomials whose coefficients all lie in `𝔄`. -/
noncomputable def coeffIdeal : Ideal (LaurentPolynomial A) :=
  RingHom.ker (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk 𝔄) :
    LaurentPolynomial A →+* LaurentPolynomial (A ⧸ 𝔄))

variable {𝔄}

theorem mem_coeffIdeal {f : LaurentPolynomial A} : f ∈ coeffIdeal 𝔄 ↔ ∀ n, f.coeff n ∈ 𝔄 := by
  rw [coeffIdeal, RingHom.mem_ker]
  constructor
  · intro h n
    have h' := congrArg (fun g : LaurentPolynomial (A ⧸ 𝔄) => g.coeff n) h
    simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at h'
    exact Ideal.Quotient.eq_zero_iff_mem.1 h'
  · intro h
    refine LaurentPolynomial.ext fun n => ?_
    rw [AddMonoidAlgebra.coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem.2 (h n),
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem coeffIdeal_le_horrB {f : LaurentPolynomial A} (hf : f ∈ coeffIdeal 𝔄) :
    f ∈ Graded.horrB 𝔄 :=
  Graded.mem_horrB.2 fun n _ => mem_coeffIdeal.1 hf n

theorem C_mem_coeffIdeal {a : A} (ha : a ∈ 𝔄) : LaurentPolynomial.C a ∈ coeffIdeal 𝔄 := by
  refine mem_coeffIdeal.2 fun n => ?_
  rw [← single_eq_C, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs
  · exact ha
  · exact 𝔄.zero_mem

theorem coeff_T_mul (k n : ℤ) (f : LaurentPolynomial A) : (T k * f).coeff n = f.coeff (n - k) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_add_eq_sub]

theorem T_neg_mem (k : ℕ) : (T (-(k : ℤ)) : LaurentPolynomial A) ∈ Graded.horrB 𝔄 := by
  refine Graded.mem_horrB.2 fun n hn => ?_
  rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (by omega)]
  exact 𝔄.zero_mem

/-- The largest positive degree of `f` (`0` if there is none). -/
noncomputable def topDeg (f : LaurentPolynomial A) : ℕ :=
  f.coeff.support.sup fun n => n.toNat

theorem coeff_eq_zero_of_topDeg_lt {f : LaurentPolynomial A} {n : ℤ} (hn : (topDeg f : ℤ) < n) :
    f.coeff n = 0 := by
  by_contra h
  have hmem : n ∈ f.coeff.support := Finsupp.mem_support_iff.2 h
  have hle : n.toNat ≤ topDeg f := Finset.le_sup (f := fun n : ℤ => n.toNat) hmem
  omega

theorem T_neg_mul_mem {f : LaurentPolynomial A} {j : ℕ} (hj : topDeg f ≤ j) :
    T (-(j : ℤ)) * f ∈ Graded.horrB 𝔄 := by
  refine Graded.mem_horrB.2 fun n hn => ?_
  rw [coeff_T_mul, coeff_eq_zero_of_topDeg_lt (f := f) (n := n - -(j : ℤ)) (by omega)]
  exact 𝔄.zero_mem

theorem exists_T_neg_mul_mem (f : LaurentPolynomial A) :
    ∃ j : ℕ, ∀ j' : ℕ, j ≤ j' → T (-(j' : ℤ)) * f ∈ Graded.horrB 𝔄 :=
  ⟨topDeg f, fun _ hj => T_neg_mul_mem hj⟩

/-- For a column `v` over `R` there is `j` with `T⁻ʲ' v ∈ Bᴺ` for all `j' ≥ j`. -/
theorem exists_T_neg_smul_mem {N : ℕ} (v : Fin N → LaurentPolynomial A) :
    ∃ j : ℕ, ∀ j' : ℕ, j ≤ j' → ∀ i, T (-(j' : ℤ)) * v i ∈ Graded.horrB 𝔄 :=
  ⟨Finset.univ.sup fun i => topDeg (v i), fun _ hj i =>
    T_neg_mul_mem (le_trans (Finset.le_sup (f := fun i => topDeg (v i)) (Finset.mem_univ i)) hj)⟩

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
