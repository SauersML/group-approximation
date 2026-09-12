import GroupApproximation.Analysis.VoiculescuCompactSqrt

/-!
# The stage estimate: one step of the monotone unit is asymptotically central

`improveUnit e f = e + √(1-e) f √(1-e)` is the step that restores monotonicity
to a quasicentral approximate unit.  This module proves the estimate the
recursion runs on: as `f` runs along a sequential approximate unit that is
asymptotically central for `S`, the improved element is asymptotically central
for `S` too — **with no constraint relating the stage to its predecessor**.

## The identity, and where compactness enters

`VoiculescuMonotoneStep.one_sub_improveUnit` gives `1 - improveUnit e f`
`= g (1-f) g` exactly, with `g = √(1-e)`.  Commutators do not see the `1`, so the
commutator of the improved element is the commutator of `g (1-f) g`, which
splits as

    `g · x (gS - Sg)  +  g (xS - Sx) g  +  (gS - Sg) x · g` ,  `x = 1 - f` .

The middle term is `‖g‖² ‖[f, S]‖`, small because `f` is quasicentral.  The outer
two contain `x` **beside** `[g, S]`, i.e. `[g,S] - f [g,S]` and
`[g,S] - [g,S] f`, and those are small because `[g, S]` is compact and `f`
absorbs compacts — `SequentialCompactUnit.tendsto_left` and `tendsto_right`.
Their smallness therefore does not depend on the size of `‖[g, S]‖`, which is the
whole point: the tolerance reachable at this stage is unconstrained by the
tolerance already spent at earlier ones, and the recursion's schedule can be
chosen forwards.

`VoiculescuCompactSqrt.isCompactOperator_commutator_sqrt_one_sub` is what
supplies the compactness, and it is the only place `e` being compact is used.

## Stated where each piece belongs

`norm_commutator_conjugate_le` is a ring identity followed by the triangle
inequality and submultiplicativity, so it is proved at an abstract C⋆-algebra;
the `B(H)` theorem only feeds it the operators.  That split is the standing
remedy in this lane for the instance towers that `B(H)`-level algebra drags in.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-! ## The algebraic estimate -/

/-- **The conjugated commutator splits into three.**  A ring identity and the
triangle inequality; no order, no calculus, no Hilbert space. -/
theorem norm_commutator_conjugate_le {A : Type*} [CStarAlgebra A] (g x S : A) :
    ‖g * x * g * S - S * (g * x * g)‖
      ≤ ‖g‖ * ‖x * (g * S - S * g)‖ + ‖g‖ * ‖x * S - S * x‖ * ‖g‖
        + ‖(g * S - S * g) * x‖ * ‖g‖ := by
  have hid : g * x * g * S - S * (g * x * g)
      = g * (x * (g * S - S * g)) + g * (x * S - S * x) * g
        + (g * S - S * g) * x * g := by
    noncomm_ring
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_mul_le _ _) ?_)) (norm_mul_le _ _))
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

/-! ## The stage estimate at `B(H)` -/

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The stage estimate.**  If `f` runs along a sequential approximate unit for
the compacts that is asymptotically central for `S`, then `improveUnit e f` is
asymptotically central for `S`, for every fixed positive compact contraction
`e`.  The rate is not uniform in `e`, and does not need to be: the recursion
picks one `e` per stage and then chooses how far along the unit to go. -/
theorem tendsto_norm_commutator_improveUnit (u : SequentialCompactUnit H)
    {e : H →L[ℂ] H} (he1 : e ≤ 1) (heK : IsCompactOperator e) (S : H →L[ℂ] H)
    (hq : Tendsto (fun n ↦ ‖u.toFun n * S - S * u.toFun n‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖improveUnit e (u.toFun n) * S - S * improveUnit e (u.toFun n)‖)
      atTop (𝓝 0) := by
  have hKc : IsCompactOperator
      ((CFC.sqrt (1 - e) * S - S * CFC.sqrt (1 - e) : H →L[ℂ] H)) :=
    isCompactOperator_commutator_sqrt_one_sub he1 heK S
  have hleft := u.tendsto_left (CFC.sqrt (1 - e) * S - S * CFC.sqrt (1 - e)) hKc
  have hright := u.tendsto_right (CFC.sqrt (1 - e) * S - S * CFC.sqrt (1 - e)) hKc
  set q : H →L[ℂ] H := CFC.sqrt (1 - e) with hqdef
  set K : H →L[ℂ] H := q * S - S * q with hKdef
  have hbound : ∀ n, ‖improveUnit e (u.toFun n) * S - S * improveUnit e (u.toFun n)‖
      ≤ ‖q‖ * ‖K - u.toFun n * K‖ + ‖q‖ * ‖u.toFun n * S - S * u.toFun n‖ * ‖q‖
        + ‖K - K * u.toFun n‖ * ‖q‖ := by
    intro n
    have hstep : improveUnit e (u.toFun n) * S - S * improveUnit e (u.toFun n)
        = -(q * (1 - u.toFun n) * q * S - S * (q * (1 - u.toFun n) * q)) := by
      have h := one_sub_improveUnit (e := e) (f := u.toFun n) he1
      rw [hqdef, ← h]
      noncomm_ring
    have hx1 : (1 - u.toFun n) * K = K - u.toFun n * K := by
      rw [sub_mul, one_mul]
    have hx2 : (1 - u.toFun n) * S - S * (1 - u.toFun n)
        = -(u.toFun n * S - S * u.toFun n) := by
      rw [sub_mul, mul_sub, one_mul, mul_one]
      abel
    have hx3 : K * (1 - u.toFun n) = K - K * u.toFun n := by
      rw [mul_sub, mul_one]
    have hmain := norm_commutator_conjugate_le q (1 - u.toFun n) S
    rw [← hKdef, hx1, hx2, hx3, norm_neg] at hmain
    rw [hstep, norm_neg]
    exact hmain
  have hzero : Tendsto (fun n ↦ ‖q‖ * ‖K - u.toFun n * K‖
      + ‖q‖ * ‖u.toFun n * S - S * u.toFun n‖ * ‖q‖
      + ‖K - K * u.toFun n‖ * ‖q‖) atTop (𝓝 0) := by
    have h := ((hleft.const_mul ‖q‖).add ((hq.const_mul ‖q‖).mul_const ‖q‖)).add
      (hright.mul_const ‖q‖)
    simpa using h
  exact squeeze_zero (fun n ↦ norm_nonneg _) hbound hzero

/-- **The stage selector, in the form the recursion calls.**  Given a finite
family and any tolerance, some single member of the unit improves `e` to an
element commuting with the whole family to within that tolerance.  The tolerance
is arbitrary and unrelated to anything about `e`, which is what lets the
recursion fix its schedule in advance. -/
theorem exists_improveUnit_norm_commutator_lt (u : SequentialCompactUnit H)
    {e : H →L[ℂ] H} (he1 : e ≤ 1) (heK : IsCompactOperator e)
    (S : ℕ → (H →L[ℂ] H)) (F : Finset ℕ)
    (hq : ∀ k, Tendsto (fun n ↦ ‖u.toFun n * S k - S k * u.toFun n‖) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∀ k ∈ F,
      ‖improveUnit e (u.toFun n) * S k - S k * improveUnit e (u.toFun n)‖ < ε := by
  classical
  choose N hN using fun k : ℕ ↦ Metric.tendsto_atTop.1
    (tendsto_norm_commutator_improveUnit u he1 heK (S k) (hq k)) ε hε
  refine ⟨F.sup N, fun k hk ↦ ?_⟩
  have h := hN k (F.sup N) (Finset.le_sup hk)
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h

end

end ShulmanFill
end GroupApproximation
