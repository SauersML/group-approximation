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
  have hip : i ≤ p := Nat.lt_add_one_iff.mp (Finset.mem_range.mp hi)
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

/-- Left Witt multiplication by a constant preserves weight-polynomiality. -/
theorem eHighWittLin_isWP_mul {w : σ → ℕ} {co : N → σ → L} (a : eHighWitt_W2 L p)
    {g : N → eHighWitt_W2 L p} (hg : eHighWittLin_IsWP w co g) :
    eHighWittLin_IsWP w co (fun x => eHighWittLin_mul a (g x)) := by
  obtain ⟨Φ₀, Φ₁, h₀, h₁, hΦ⟩ := hg
  have hp : IsWeightedHomogeneous (eHighWitt_hwt w) (Φ₀ ^ p) p :=
    eHighWitt_isWH_of_eq (h₀.pow p) (by simp only [smul_eq_mul, mul_one])
  refine ⟨C a.x0 * Φ₀, C (a.x0 ^ p) * Φ₁ + C a.x1 * Φ₀ ^ p, h₀.C_mul _,
    (h₁.C_mul _).add (hp.C_mul _), fun x => ⟨?_, ?_⟩⟩
  · show a.x0 * (g x).x0 = aeval (eHighWitt_hpt (co x)) (C a.x0 * Φ₀)
    simp only [map_mul, aeval_C, Algebra.algebraMap_self_apply, (hΦ x).1]
  · show a.x0 ^ p * (g x).x1 + a.x1 * (g x).x0 ^ p =
      aeval (eHighWitt_hpt (co x)) (C (a.x0 ^ p) * Φ₁ + C a.x1 * Φ₀ ^ p)
    simp only [map_add, map_mul, map_pow, aeval_C, Algebra.algebraMap_self_apply, (hΦ x).1,
      (hΦ x).2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWP_mul

/-- Finite sums, in the group `W₂(L)`, of weight-polynomial maps are weight-polynomial. -/
theorem eHighWittLin_isWP_sum [Fact p.Prime] {ι : Type} {w : σ → ℕ} {co : N → σ → L}
    (s : Finset ι) (f : ι → N → eHighWitt_W2 L p)
    (hf : ∀ i ∈ s, eHighWittLin_IsWP w co (f i)) :
    eHighWittLin_IsWP w co (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact eHighWittLin_isWP_zero w co
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact eHighWittLin_isWP_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWP_sum

/-- A coordinate projection `x ↦ x j` of `W₂(L)ⁿ` is weight-polynomial. -/
theorem eHighWittLin_isWP_proj {n : ℕ} (j : Fin n) :
    eHighWittLin_IsWP (eHighWitt_wt p n)
      (eHighWitt_coord : (Fin n → eHighWitt_W2 L p) → Fin n ⊕ Fin n → L)
      (fun x => x j) :=
  ⟨X (some (Sum.inl j)), X (some (Sum.inr j)), isWeightedHomogeneous_X L _ _,
    isWeightedHomogeneous_X L _ _, fun x =>
      ⟨(aeval_X (R := L) (eHighWitt_hpt (eHighWitt_coord x)) (some (Sum.inl j))).symm,
        (aeval_X (R := L) (eHighWitt_hpt (eHighWitt_coord x)) (some (Sum.inr j))).symm⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_isWP_proj

/-- The action of a `W₂(L)`-matrix on `W₂(L)ⁿ`: `x ↦ (∑ₗ A i l * x l)ᵢ`. -/
def eHighWittLin_mulVec [Fact p.Prime] {n : ℕ} (A : Fin n → Fin n → eHighWitt_W2 L p)
    (x : Fin n → eHighWitt_W2 L p) : Fin n → eHighWitt_W2 L p :=
  fun i => ∑ l, eHighWittLin_mul (A i l) (x l)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_mulVec

/-- **Endpoint (proved outright).**  Every `W₂(L)`-matrix action is weight-polynomial for the
Witt weights. -/
theorem eHighWittLin_mulVec_isWeightPoly [Fact p.Prime] {n : ℕ}
    (A : Fin n → Fin n → eHighWitt_W2 L p) :
    eHighWitt_IsWeightPoly (eHighWitt_wt p n) eHighWitt_coord (eHighWittLin_mulVec A) := by
  have h : ∀ i : Fin n, eHighWittLin_IsWP (eHighWitt_wt p n) eHighWitt_coord
      (fun x : Fin n → eHighWitt_W2 L p => eHighWittLin_mulVec A x i) := fun i =>
    eHighWittLin_isWP_sum Finset.univ
      (fun (l : Fin n) (x : Fin n → eHighWitt_W2 L p) => eHighWittLin_mul (A i l) (x l))
      (fun l _ => eHighWittLin_isWP_mul (A i l) (eHighWittLin_isWP_proj l))
  intro v
  cases v with
  | inl i =>
    obtain ⟨Φ₀, _, h₀, _, hΦ⟩ := h i
    exact ⟨Φ₀, h₀, fun x => (hΦ x).1⟩
  | inr i =>
    obtain ⟨_, Φ₁, _, h₁, hΦ⟩ := h i
    exact ⟨Φ₁, h₁, fun x => (hΦ x).2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittLin_mulVec_isWeightPoly

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
