import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Nat.Prime.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# R1 over `ℤ[1/m]`: the leading-coefficient ideal and primewise monicity

Lane `bh-met-90w`.  Pure commutative algebra, no matrices.  For an ideal `I ⊆ A[X]`,
`suslinR1Int_leadIdeal I D` is the ideal of degree-`D` coefficients of members of `I` of
degree `≤ D`; these increase with `D` (multiply by `X`), so their union
`suslinR1Int_leadSup I` is an ideal, and it contains the leading coefficient of every
member of `I`.  If `1` lies in it, `I` contains a MONIC polynomial.

`suslinR1Int_monic_of_primewise`: if `I` contains a polynomial with leading coefficient a
positive integer `c`, and for every prime `p ∣ c` a polynomial whose leading coefficient is
coprime to `p`, then `I` contains a monic polynomial.  (A maximal ideal containing the
leading-coefficient ideal would contain `c`, hence some prime `p ∣ c`.)
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A]

/-- The degree-`D` coefficients of the members of `I` of degree at most `D`. -/
def suslinR1Int_leadIdeal (I : Ideal (Polynomial A)) (D : ℕ) : Ideal A where
  carrier := {ℓ | ∃ q ∈ I, q.natDegree ≤ D ∧ q.coeff D = ℓ}
  add_mem' := by
    rintro _ _ ⟨q₁, h₁, d₁, rfl⟩ ⟨q₂, h₂, d₂, rfl⟩
    exact ⟨q₁ + q₂, I.add_mem h₁ h₂, Polynomial.natDegree_add_le_of_degree_le d₁ d₂,
      Polynomial.coeff_add q₁ q₂ D⟩
  zero_mem' := ⟨0, I.zero_mem, by simp, by simp⟩
  smul_mem' := by
    rintro a _ ⟨q, hq, hd, rfl⟩
    exact ⟨Polynomial.C a * q, I.mul_mem_left _ hq,
      (Polynomial.natDegree_C_mul_le a q).trans hd,
      by rw [Polynomial.coeff_C_mul, smul_eq_mul]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_leadIdeal

theorem suslinR1Int_mem_leadIdeal {I : Ideal (Polynomial A)} {D : ℕ} {ℓ : A} :
    ℓ ∈ suslinR1Int_leadIdeal I D ↔ ∃ q ∈ I, q.natDegree ≤ D ∧ q.coeff D = ℓ :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_mem_leadIdeal

/-- The coefficient ideals increase with the degree bound (multiply by a power of `X`). -/
theorem suslinR1Int_leadIdeal_mono (I : Ideal (Polynomial A)) :
    Monotone (suslinR1Int_leadIdeal I) := by
  intro D E hDE ℓ hℓ
  obtain ⟨q, hq, hd, rfl⟩ := suslinR1Int_mem_leadIdeal.1 hℓ
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hDE
  refine suslinR1Int_mem_leadIdeal.2
    ⟨Polynomial.X ^ e * q, I.mul_mem_left _ hq, ?_, Polynomial.coeff_X_pow_mul q e D⟩
  have h1 := Polynomial.natDegree_mul_le (p := (Polynomial.X ^ e : Polynomial A)) (q := q)
  have h2 := Polynomial.natDegree_X_pow_le (R := A) e
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_leadIdeal_mono

/-- The leading-coefficient ideal of `I`. -/
def suslinR1Int_leadSup (I : Ideal (Polynomial A)) : Ideal A :=
  ⨆ D : ℕ, suslinR1Int_leadIdeal I D

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_leadSup

theorem suslinR1Int_mem_leadSup {I : Ideal (Polynomial A)} {ℓ : A} :
    ℓ ∈ suslinR1Int_leadSup I ↔ ∃ D, ℓ ∈ suslinR1Int_leadIdeal I D := by
  unfold suslinR1Int_leadSup
  exact Submodule.mem_iSup_of_directed _ (suslinR1Int_leadIdeal_mono I).directed_le

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_mem_leadSup

theorem suslinR1Int_lc_mem_leadSup {I : Ideal (Polynomial A)} {q : Polynomial A}
    (hq : q ∈ I) : q.leadingCoeff ∈ suslinR1Int_leadSup I :=
  suslinR1Int_mem_leadSup.2 ⟨q.natDegree, suslinR1Int_mem_leadIdeal.2
    ⟨q, hq, le_rfl, Polynomial.coeff_natDegree⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_lc_mem_leadSup

/-- If `1` is a leading coefficient in the ideal sense, `I` contains a monic polynomial. -/
theorem suslinR1Int_monic_of_one_mem {I : Ideal (Polynomial A)}
    (h : (1 : A) ∈ suslinR1Int_leadSup I) : ∃ q ∈ I, q.Monic := by
  obtain ⟨D, hD⟩ := suslinR1Int_mem_leadSup.1 h
  obtain ⟨q, hq, hd, h1⟩ := suslinR1Int_mem_leadIdeal.1 hD
  exact ⟨q, hq, Polynomial.monic_of_natDegree_le_of_coeff_eq_one D hd h1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_monic_of_one_mem

/-- A prime ideal containing a positive integer `n` contains a prime divisor of `n`. -/
theorem suslinR1Int_exists_prime_mem (P : Ideal A) (hP : P.IsPrime) :
    ∀ n : ℕ, 0 < n → (n : A) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : A) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hpr := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hmem' : (n.minFac : A) * (k : A) ∈ P := by
        rw [← Nat.cast_mul, ← hk]
        exact hmem
      rcases hP.mem_or_mem hmem' with hp | hkP
      · exact ⟨n.minFac, hpr, Nat.minFac_dvd n, hp⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero (by
          rintro rfl
          rw [mul_zero] at hk
          omega)
        have hlt : k < n := calc
          k < 2 * k := by omega
          _ ≤ n.minFac * k := Nat.mul_le_mul_right k hpr.two_le
          _ = n := hk.symm
        obtain ⟨p, hp, hpk, hpP⟩ := ih k hlt hkpos hkP
        exact ⟨p, hp, hpk.trans (Dvd.intro_left n.minFac hk.symm), hpP⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Int_exists_prime_mem

