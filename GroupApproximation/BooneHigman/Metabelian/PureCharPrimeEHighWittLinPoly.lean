import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoord
import GroupApproximation.Meta.AxiomGuard

/-!
# Witt-matrix actions are weight-polynomial (bh-met-87d, part 1)

`eHighWittLin_mul a x = (a₀ x₀, a₀^p x₁ + a₁ x₀^p)` is the length-two Witt product on the
explicit model `eHighWitt_W2 L p`.  For a matrix `A` with entries in the model,
`eHighWittLin_mulVec A x = (∑ₗ A i l * x l)ᵢ`, with the sum taken in the additive group
`eHighWitt_W2 L p`.

**Proved outright.**  `eHighWittLin_mulVec_isWeightPoly`: every such map is weight-polynomial for
the Witt weights `eHighWitt_wt p n` (weight `1` on `x₀`, weight `p` on `x₁`).  The zeroth
coordinate is homogenized of weight `1` and the first of weight `p`.  This closes, by explicit
polynomials, the weight bookkeeping that `EHighArtinHasseWittEmbedStatement` needs.

Closure facts used: sums (the carry `((a+b)^p - a^p - b^p)/p` has weight `p` when `a`, `b` have
weight `1`), products with a constant, and coordinate projections.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open MvPolynomial

noncomputable section

variable {L : Type} [Field L] {p : ℕ} {σ N : Type}

/-- The length-two Witt product `(a₀ x₀, a₀^p x₁ + a₁ x₀^p)` on the explicit model. -/
def eHighWittLin_mul (a x : eHighWitt_W2 L p) : eHighWitt_W2 L p :=
  ⟨a.x0 * x.x0, a.x0 ^ p * x.x1 + a.x1 * x.x0 ^ p⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_mul

/-- `g : N → W₂(L)` is weight-polynomial: `x₀ ∘ g` is homogenized of weight `1` and `x₁ ∘ g` of
weight `p`, in the coordinates `co`. -/
def eHighWittLin_IsWP (w : σ → ℕ) (co : N → σ → L) (g : N → eHighWitt_W2 L p) : Prop :=
  ∃ Φ₀ Φ₁ : MvPolynomial (Option σ) L,
    IsWeightedHomogeneous (eHighWitt_hwt w) Φ₀ 1 ∧
      IsWeightedHomogeneous (eHighWitt_hwt w) Φ₁ p ∧
        ∀ x : N, (g x).x0 = aeval (eHighWitt_hpt (co x)) Φ₀ ∧
          (g x).x1 = aeval (eHighWitt_hpt (co x)) Φ₁

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_IsWP

theorem eHighWittLin_isWH_sub {τ : Type} {w : τ → ℕ} {Φ Ψ : MvPolynomial τ L} {d : ℕ}
    (hΦ : IsWeightedHomogeneous w Φ d) (hΨ : IsWeightedHomogeneous w Ψ d) :
    IsWeightedHomogeneous w (Φ - Ψ) d :=
  (mem_weightedHomogeneousSubmodule L w d (Φ - Ψ)).mp
    (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule L w d Φ).mpr hΦ)
      ((mem_weightedHomogeneousSubmodule L w d Ψ).mpr hΨ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWH_sub

/-- The carry of two weight-`1` polynomials has weight `p`. -/
theorem eHighWittLin_isWH_carry {τ : Type} {w : τ → ℕ} {Φ Ψ : MvPolynomial τ L}
    (hΦ : IsWeightedHomogeneous w Φ 1) (hΨ : IsWeightedHomogeneous w Ψ 1) :
    IsWeightedHomogeneous w (eHighWitt_carry p Φ Ψ) p := by
  rw [eHighWitt_carry]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
  have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : ((p.choose i / p : ℕ) : MvPolynomial τ L) =
      C ((p.choose i / p : ℕ) : L) :=
    (map_natCast (C : L →+* MvPolynomial τ L) (p.choose i / p)).symm
  have key : IsWeightedHomogeneous w
      (C ((p.choose i / p : ℕ) : L) * Φ ^ i * Ψ ^ (p - i)) p :=
    eHighWitt_isWH_of_eq (((hΦ.pow i).C_mul _).mul (hΨ.pow (p - i)))
      (by simp only [smul_eq_mul, mul_one]; omega)
  rw [← hc] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWH_carry

theorem eHighWittLin_aeval_carry {τ : Type} (pt : τ → L) (Φ Ψ : MvPolynomial τ L) :
    aeval pt (eHighWitt_carry p Φ Ψ) = eHighWitt_carry p (aeval pt Φ) (aeval pt Ψ) := by
  simp only [eHighWitt_carry, map_sum, map_mul, map_pow, map_natCast]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_aeval_carry

theorem eHighWittLin_isWP_zero (w : σ → ℕ) (co : N → σ → L) :
    eHighWittLin_IsWP w co (fun _ => (0 : eHighWitt_W2 L p)) :=
  ⟨0, 0, isWeightedHomogeneous_zero L _ _, isWeightedHomogeneous_zero L _ _, fun x =>
    ⟨(map_zero (aeval (R := L) (eHighWitt_hpt (co x)))).symm,
      (map_zero (aeval (R := L) (eHighWitt_hpt (co x)))).symm⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWP_zero

theorem eHighWittLin_isWP_add {w : σ → ℕ} {co : N → σ → L} {g h : N → eHighWitt_W2 L p}
    (hg : eHighWittLin_IsWP w co g) (hh : eHighWittLin_IsWP w co h) :
    eHighWittLin_IsWP w co (fun x => g x + h x) := by
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦ⟩ := hg
  obtain ⟨Ψ₀, Ψ₁, hΨ₀, hΨ₁, hΨ⟩ := hh
  refine ⟨Φ₀ + Ψ₀, Φ₁ + Ψ₁ - eHighWitt_carry p Φ₀ Ψ₀, hΦ₀.add hΨ₀,
    eHighWittLin_isWH_sub (hΦ₁.add hΨ₁) (eHighWittLin_isWH_carry hΦ₀ hΨ₀),
    fun x => ⟨?_, ?_⟩⟩
  · show (g x).x0 + (h x).x0 = aeval (eHighWitt_hpt (co x)) (Φ₀ + Ψ₀)
    rw [map_add, (hΦ x).1, (hΨ x).1]
  · show (g x).x1 + (h x).x1 - eHighWitt_carry p (g x).x0 (h x).x0 =
      aeval (eHighWitt_hpt (co x)) (Φ₁ + Ψ₁ - eHighWitt_carry p Φ₀ Ψ₀)
    rw [map_sub, map_add, eHighWittLin_aeval_carry, (hΦ x).1, (hΨ x).1, (hΦ x).2, (hΨ x).2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWP_add

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
