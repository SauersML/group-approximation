import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittPoly
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Ring.Finset
import GroupApproximation.Meta.AxiomGuard

/-!
# Padded weight-polynomial functions (bh-met-87h, part 8)

Fix coordinates `co : N → σ → L` and weights `w : σ → ℕ`. A function `f : N → L` is
`D`-padded (`eHighWittE_Pad w co D f`) if `f x = Φ(1, co x)` for a homogenized `Φ` of weighted
degree exactly `D`. The extra variable has weight `1`, so this means weighted degree `≤ D`.

Padded functions are closed under the following operations.

* Constants, `+`, `*` (degrees add), powers, finite sums and products.
* Raising the degree (`eHighWittE_pad_mono`).
* Substitution into an integer polynomial `R` of total degree `r`: if each `f t` is
  `D₀`-padded and `r * D₀ ≤ E`, then `x ↦ R(f t x)` is `E`-padded (`eHighWittE_pad_subst`).

Weight-polynomial maps are exactly those with `w v`-padded coordinates
(`eHighWittE_isWeightPoly_of_pad`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

variable {L : Type} [Field L] {σ : Type} {N : Type} {w : σ → ℕ} {co : N → σ → L}

/-- `f` is a homogenized polynomial of weighted degree `D` in the coordinates. -/
def eHighWittE_Pad (w : σ → ℕ) (co : N → σ → L) (D : ℕ) (f : N → L) : Prop :=
  ∃ Φ : MvPolynomial (Option σ) L, IsWeightedHomogeneous (eHighWitt_hwt w) Φ D ∧
    ∀ x : N, f x = aeval (eHighWitt_hpt (co x)) Φ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_Pad

theorem eHighWittE_pad_of_eq {D : ℕ} {f g : N → L} (hf : eHighWittE_Pad w co D f)
    (h : ∀ x, f x = g x) : eHighWittE_Pad w co D g := by
  obtain ⟨Φ, hΦ, hfΦ⟩ := hf
  exact ⟨Φ, hΦ, fun x => (h x).symm.trans (hfΦ x)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_of_eq

theorem eHighWittE_pad_const (D : ℕ) (c : L) : eHighWittE_Pad w co D (fun _ => c) := by
  refine ⟨C c * X none ^ D,
    eHighWitt_isWH_of_eq ((eHighWitt_isWH_X_pow w none D).C_mul c) (one_mul D), fun x => ?_⟩
  rw [map_mul, map_pow, aeval_C, aeval_X, Algebra.algebraMap_self_apply]
  show c = c * (1 : L) ^ D
  rw [one_pow, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_const

theorem eHighWittE_pad_add {D : ℕ} {f g : N → L} (hf : eHighWittE_Pad w co D f)
    (hg : eHighWittE_Pad w co D g) : eHighWittE_Pad w co D (fun x => f x + g x) := by
  obtain ⟨Φ, hΦ, hfΦ⟩ := hf
  obtain ⟨Ψ, hΨ, hgΨ⟩ := hg
  exact ⟨Φ + Ψ, hΦ.add hΨ, fun x => by rw [map_add, ← hfΦ x, ← hgΨ x]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_add

theorem eHighWittE_pad_mul {D E : ℕ} {f g : N → L} (hf : eHighWittE_Pad w co D f)
    (hg : eHighWittE_Pad w co E g) : eHighWittE_Pad w co (D + E) (fun x => f x * g x) := by
  obtain ⟨Φ, hΦ, hfΦ⟩ := hf
  obtain ⟨Ψ, hΨ, hgΨ⟩ := hg
  exact ⟨Φ * Ψ, hΦ.mul hΨ, fun x => by rw [map_mul, ← hfΦ x, ← hgΨ x]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_mul

theorem eHighWittE_pad_pow {D : ℕ} {f : N → L} (hf : eHighWittE_Pad w co D f) (k : ℕ) :
    eHighWittE_Pad w co (k * D) (fun x => f x ^ k) := by
  obtain ⟨Φ, hΦ, hfΦ⟩ := hf
  exact ⟨Φ ^ k, eHighWitt_isWH_of_eq (hΦ.pow k) (smul_eq_mul k D), fun x => by
    rw [map_pow, ← hfΦ x]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_pow

theorem eHighWittE_pad_mono {D E : ℕ} {f : N → L} (hf : eHighWittE_Pad w co D f)
    (h : D ≤ E) : eHighWittE_Pad w co E f := by
  have h1 := eHighWittE_pad_mul hf (eHighWittE_pad_const (E - D) (1 : L))
  rw [Nat.add_sub_of_le h] at h1
  exact eHighWittE_pad_of_eq h1 fun x => mul_one (f x)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_mono

theorem eHighWittE_pad_sum {ι : Type} (s : Finset ι) {D : ℕ} (f : ι → N → L)
    (hf : ∀ i ∈ s, eHighWittE_Pad w co D (f i)) :
    eHighWittE_Pad w co D (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact eHighWittE_pad_of_eq (eHighWittE_pad_const D 0) fun x => by rw [Finset.sum_empty]
  | insert a s ha ih =>
    exact eHighWittE_pad_of_eq (eHighWittE_pad_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))) fun x => by
        rw [Finset.sum_insert ha]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_sum

theorem eHighWittE_pad_prod {ι : Type} (s : Finset ι) (f : ι → N → L) (D : ι → ℕ)
    (hf : ∀ i, eHighWittE_Pad w co (D i) (f i)) :
    eHighWittE_Pad w co (∑ i ∈ s, D i) (fun x => ∏ i ∈ s, f i x) := by
  choose Φ hΦ hfΦ using hf
  refine ⟨∏ i ∈ s, Φ i, IsWeightedHomogeneous.prod s Φ D fun i _ => hΦ i, fun x => ?_⟩
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => hfΦ i x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_prod

theorem eHighWittE_pad_coord (v : σ) : eHighWittE_Pad w co (w v) (fun x => co x v) :=
  ⟨X (some v), isWeightedHomogeneous_X L _ _, fun x =>
    (aeval_X (R := L) (eHighWitt_hpt (co x)) (some v)).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_coord

theorem eHighWittE_isWeightPoly_of_pad {g : N → N}
    (h : ∀ v, eHighWittE_Pad w co (w v) (fun x => co (g x) v)) :
    eHighWitt_IsWeightPoly w co g := h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isWeightPoly_of_pad

/-- **Substitution into an integer polynomial.** If each `f t` is `D₀`-padded and
`totalDegree R * D₀ ≤ E`, then `x ↦ R(f t x)` is `E`-padded. -/
theorem eHighWittE_pad_subst {τ : Type} (R : MvPolynomial τ ℤ) (f : τ → N → L) {D0 E : ℕ}
    (hf : ∀ t, eHighWittE_Pad w co D0 (f t)) (hE : R.totalDegree * D0 ≤ E) :
    eHighWittE_Pad w co E (fun x => aeval (fun t => f t x) R) := by
  refine eHighWittE_pad_of_eq (eHighWittE_pad_sum R.support
    (fun m x => algebraMap ℤ L (R.coeff m) * ∏ t ∈ m.support, f t x ^ m t) fun m hm => ?_)
    fun x => ?_
  · have hle : (∑ t ∈ m.support, m t * D0) ≤ E := by
      rw [← Finset.sum_mul]
      exact le_trans (Nat.mul_le_mul_right D0 (le_totalDegree hm)) hE
    exact eHighWittE_pad_mono (eHighWittE_pad_mul (eHighWittE_pad_const 0 _)
      (eHighWittE_pad_prod m.support (fun t x => f t x ^ m t) (fun t => m t * D0)
        fun t => eHighWittE_pad_pow (hf t) (m t))) ((zero_add _).trans_le hle)
  · exact (eval₂_eq (algebraMap ℤ L) (fun t => f t x) R).symm.trans (aeval_def R).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_pad_subst

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
