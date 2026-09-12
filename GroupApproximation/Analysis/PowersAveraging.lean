import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# Powers' averaging argument: the C⋆ half, proved

Powers' theorem — the reduced C⋆-algebra of a free group of rank at least two is
simple — has four components.  This module proves the last one and names the
first.

* **(A)** `adjoin ℂ (range λ) = span ℂ (range λ)`, because the range of the left
  regular representation is a submonoid closed under `star`.
* **(B)** The *Powers property* of a free group of rank at least two: for every
  finite `F ⊆ G \ {1}` and every `n`, a partition `G = C ⊔ D` and elements
  `g₁, …, gₙ` with `fC ∩ C = ∅` for `f ∈ F` and the `gᵢD` pairwise disjoint.
  Combinatorics on reduced words.
* **(C)** The **averaging estimate**: for `a` in the kernel of the canonical
  trace, the averages `(1/n) Σ λ(gᵢ) a λ(gᵢ)*` have small norm.
* **(D)** From (C), every nonzero closed two-sided ideal contains an invertible
  element, so the algebra is simple.

**(C) is the analytic core of Powers' theorem and it is NAMED HERE, NOT PROVED.**
`PowersAveragingEstimate` is a hypothesis of everything below.  Nobody should
read this module as Powers being done: what is done is the C⋆-algebra argument
*around* the estimate.

**Where (C) is proved.**  Not here, but downstream, and unconditionally on
(B): `Analysis/GroupHilbertSubsetProjection` builds the projections of `ℓ²(G)`
onto the subsets of a partition (as the landed `CStarExactness.mulOp` at an
indicator symbol), `Analysis/OrthogonalProjectionSumEstimate` supplies the
`1/√n` gain from almost-orthogonality (as the landed
`ShulmanFill.norm_sum_sq_le_of_almostOrthogonal` at off-diagonal size zero),
`Analysis/PowersAveragingFromPartition` assembles the two into the estimate at a
fixed partition, and `Analysis/PowersAveragingFromPowersProperty` closes the
density and identity-coefficient bookkeeping.  What is left is (B) alone.

**Also proved downstream:** the estimate gives the *unique trace* as well as
simplicity — `Analysis/PowersAveragingUniqueTrace` — so a route carrying the
estimate does not need Breuillard--Kalantar--Kennedy--Ozawa.

## Why (A) and (B) do not appear as hypotheses

`PowersAveragingEstimate` is stated for **every** element of the kernel of the
trace, not only for the finitely supported ones.  By density the two forms are
equivalent, and the stronger one is the cleaner statement — so the assembly below
never has to pass from a finite sum to a general element, and (A) is not needed
here at all.  (B) is the combinatorial input to a *proof* of (C), so it sits
behind that Prop rather than beside it.

## What (D) rests on, and it is already here

The faithfulness of the canonical trace, `canonicalFaithfulTracialState`, is what
makes the argument start: it turns "`x ≠ 0`" into "`τ(x*x) ≠ 0`", which is the
only way to know there is anything to normalise.  A merely positive trace would
not do.

## The argument

Let `I` be a nonzero closed two-sided ideal and `0 ≠ x ∈ I`.  Then `x*x ∈ I` is
positive, and nonzero *by faithfulness*, so `t := τ(x*x)` is a positive real.
Normalise: `c := t⁻¹ • (x*x) ∈ I` has `τ(c) = 1`, so `a := c - 1` lies in the
kernel of the trace.  Apply the estimate at `ε = 1/2`.  Averaging fixes `1`,
because each `λ(gᵢ)` is a unitary and `(1/n) Σ 1 = 1`, so

  `‖avg(c) - 1‖ = ‖avg(a)‖ ≤ 1/2 < 1`,

which makes `avg(c)` invertible; and `avg(c) ∈ I` because an ideal is closed
under `u · _ · u*` and under sums and scalars.  An ideal containing a unit is
everything.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open scoped ComplexOrder

universe u

variable (G : Type u) [Group G]

/-! ## The averaging estimate, as a named hypothesis -/

/-- **Powers' averaging estimate** — component (C), the analytic core, stated and
**not proved**.

For every element `a` killed by the canonical trace and every `ε > 0`, some
finite averaging by unitaries of the group brings `a` inside the ball of radius
`ε`.  For a free group of rank at least two this is Powers' estimate, whose
proof runs through the Powers property (component (B)) and a `1/√n` gain from
almost-orthogonality. -/
def PowersAveragingEstimate : Prop :=
  ∀ a : ReducedGroupCStar G, canonicalFaithfulTracialState G a = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (g : Fin n → G), 0 < n ∧
        ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))‖ ≤ ε

/-! ## Averaging fixes the unit -/

/-- Each `λ(g)` is a unitary of `C*_r(G)`: `λ(g) λ(g)* = 1`.

Proved from `star_reducedLeftRegular` and multiplicativity rather than by
projecting the `unitary` membership of `reducedLeftRegularUnitary`, whose two
conjuncts are `star u * u = 1` first and `u * star u = 1` second at this Mathlib
pin — reading them the other way round is what made an earlier version of this
module red. -/
theorem reducedLeftRegular_mul_star (g : G) :
    reducedLeftRegular G g * star (reducedLeftRegular G g) = 1 := by
  rw [star_reducedLeftRegular, ← reducedLeftRegular_mul, mul_inv_cancel,
    reducedLeftRegular_one]

/-- The companion identity `λ(g)* λ(g) = 1`. -/
theorem star_reducedLeftRegular_mul (g : G) :
    star (reducedLeftRegular G g) * reducedLeftRegular G g = 1 := by
  rw [star_reducedLeftRegular, ← reducedLeftRegular_mul, inv_mul_cancel,
    reducedLeftRegular_one]

/-- **Averaging fixes `1`.**  Conjugating the unit by unitaries and averaging
returns the unit; this is what makes `avg(c) - 1 = avg(c - 1)`. -/
theorem average_one (n : ℕ) (hn : 0 < n) (g : Fin n → G) :
    ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * (1 : ReducedGroupCStar G) *
          star (reducedLeftRegular G (g i))) = 1 := by
  have hterm : ∀ i : Fin n,
      reducedLeftRegular G (g i) * (1 : ReducedGroupCStar G) *
        star (reducedLeftRegular G (g i)) = 1 := by
    intro i
    rw [mul_one, reducedLeftRegular_mul_star]
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne,
    one_smul]

/-- **Averaging is additive**, in the form the argument uses: the average of
`c - 1` is the average of `c`, less `1`. -/
theorem average_sub_one (n : ℕ) (hn : 0 < n) (g : Fin n → G)
    (c : ReducedGroupCStar G) :
    ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * (c - 1) * star (reducedLeftRegular G (g i)))
      = ((n : ℂ)⁻¹ • ∑ i : Fin n,
          reducedLeftRegular G (g i) * c * star (reducedLeftRegular G (g i))) - 1 := by
  have hsplit : ∀ i : Fin n,
      reducedLeftRegular G (g i) * (c - 1) * star (reducedLeftRegular G (g i))
        = reducedLeftRegular G (g i) * c * star (reducedLeftRegular G (g i))
          - reducedLeftRegular G (g i) * (1 : ReducedGroupCStar G) *
              star (reducedLeftRegular G (g i)) := by
    intro i
    rw [mul_sub, sub_mul]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib, smul_sub,
    average_one G n hn g]

/-! ## The ideal argument -/

/-- Averaging keeps an element inside a two-sided ideal. -/
theorem average_mem_ideal {I : Ideal (ReducedGroupCStar G)} [I.IsTwoSided]
    (n : ℕ) (g : Fin n → G) {c : ReducedGroupCStar G} (hc : c ∈ I) :
    ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * c * star (reducedLeftRegular G (g i))) ∈ I := by
  have hsum : (∑ i : Fin n,
      reducedLeftRegular G (g i) * c * star (reducedLeftRegular G (g i))) ∈ I :=
    Submodule.sum_mem _ fun i _ =>
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hsum

set_option maxHeartbeats 1000000 in
/-- **Component (D), proved: Powers' averaging estimate makes `C*_r(G)`
simple.**

The estimate is a hypothesis, not a theorem, here; everything else in the
argument is discharged. -/
theorem isSimpleCStar_of_powersAveragingEstimate
    (h : PowersAveragingEstimate G) : IsSimpleCStar (ReducedGroupCStar G) := by
  intro I hI hIclosed
  haveI := hI
  rcases eq_or_ne I ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr ?_
  -- A nonzero element of the ideal.
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  set τ := canonicalFaithfulTracialState G with hτ
  have hxxI : star x * x ∈ I := Ideal.mul_mem_left _ _ hxI
  -- Faithfulness: the trace of `x*x` is a nonzero, nonnegative complex number.
  have hnn : 0 ≤ τ (star x * x) := τ.map_star_mul_self_nonneg x
  have hne : τ (star x * x) ≠ 0 := fun hz =>
    hx0 (τ.eq_zero_of_map_star_mul_self_eq_zero hz)
  set t : ℂ := τ (star x * x) with ht
  have him : t.im = 0 := ((Complex.nonneg_iff.mp hnn).2).symm
  have hre : 0 < t.re := by
    rcases lt_or_eq_of_le (Complex.nonneg_iff.mp hnn).1 with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm him) hne
  have htre : t = (t.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  -- Normalise so the trace is `1`.
  set c : ReducedGroupCStar G := ((t.re : ℂ))⁻¹ • (star x * x) with hc
  have hcI : c ∈ I := by
    rw [hc, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ hxxI
  have hτc : τ c = 1 := by
    rw [hc, map_smul, ← ht, htre, smul_eq_mul, Complex.ofReal_re, inv_mul_cancel₀]
    exact_mod_cast hre.ne'
  have hτa : τ (c - 1) = 0 := by
    rw [map_sub, hτc, τ.map_one, sub_self]
  -- The estimate at `ε = 1/2`.
  obtain ⟨n, g, hn, hbound⟩ := h (c - 1) hτa (1 / 2) (by norm_num)
  rw [average_sub_one G n hn g c] at hbound
  set y : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * c * star (reducedLeftRegular G (g i)) with hy
  have hyI : y ∈ I := average_mem_ideal G n g hcI
  -- `‖y - 1‖ ≤ 1/2 < 1`, so `y` is invertible.
  have hlt : ‖(1 : ReducedGroupCStar G) - y‖ < 1 := by
    rw [← norm_neg, neg_sub]
    exact lt_of_le_of_lt hbound (by norm_num)
  have hunit : IsUnit y := by
    have := (Units.oneSub ((1 : ReducedGroupCStar G) - y) hlt).isUnit
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ hyI hunit

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms average_one
#audit_axioms average_sub_one
#audit_axioms average_mem_ideal
#audit_axioms isSimpleCStar_of_powersAveragingEstimate
