import GroupApproximation.Analysis.ShulmanFillConjugatePair

/-!
# The asymptotic-agreement estimate of Theorem 10, and where Lemma 9 stands

Shulman's Theorem 10 (arXiv:2603.13564v2, p. 8) needs the two asymptotic
homomorphisms `φ⁽²⁾_k` and `φ⁽¹⁾_k = V_k* φ⁽²⁾_k V_k` to agree asymptotically
on `C`, knowing only that the commutators `[V_k, φ_k(c)]` die on an exhausting
sequence of finite subsets of a dense sequence of `C`.  Her estimate is

`‖φ⁽¹⁾_k(c) − φ⁽²⁾_k(c)‖ < 4ε + ‖[V_k, φ⁽²⁾_k(c₀)]‖ < 5ε`

for `c₀` close to `c` in the dense sequence.  `tendsto_norm_unitaryConj_sub`
below is that estimate, in the form that does not mention `𝒟`: contractive
families, a dense sequence, and commutators vanishing at each fixed member of
it.  It is proved here.

## Where Lemma 9 stands in the repository

Read from the peer modules:

* **Proved, abstractly.**  `Analysis/ShulmanHalmosDilationBase` defines the
  dilation `halmos x` out of `leftDefect x = CFC.sqrt (1 - x x*)` and
  `rightDefect x = CFC.sqrt (1 - x* x)`;
  `Analysis/ShulmanHalmosDilationUnitary` proves `halmos_mem_unitary` for a
  contraction and packages `halmosUnitary`;
  `Analysis/ShulmanHalmosDilationAlgebra` proves the defect identities
  (`leftDefect_mul_eq_mul_rightDefect` and its adjoint form);
  `Analysis/ShulmanHalmosDilationCommutator` computes
  `halmos_commutator_diag₂` — the block form of `[V, diag(a,a)]` displayed in
  the paper — and bounds it by the entries
  (`norm_halmos_commutator_diag₂_le`, and a quarter-form).
  `Analysis/ShulmanHalmosDilationEndpoint` closes
  `HalmosDilationAndBlockCommutatorControl`.
* **Proved, at the corona.**  `Analysis/ShulmanCoronaHalmosSequence` builds
  `halmosSequence` and proves `halmosSequence_mem_unitary` and
  `isNull_halmosSequence_commutator`, closing `CoronaHalmosSequenceControl`;
  `Analysis/ShulmanCoronaHalmosArgumentCommutator` and
  `Analysis/ShulmanCoronaHalmosDefectRoot` prove that the commutators of the
  two defect arguments and of their square roots are null, and
  `Analysis/ShulmanCoronaSquareRoot*` supply the square-root sequences.

* **Missing: Pedersen's inequality.**  `‖[A^{1/2}, B]‖ ≤ (5/4)‖[A, B]‖^{1/2}`
  appears nowhere in the repository.  It is what converts a *quantitative*
  commutator bound on `X̃X̃*` into one on its square root, so it is needed for
  the `1/k`-at-stage-`k` form of Lemma 9 — and only for that.  The corona
  modules do not need it: there the statement is that a commutator sequence is
  *null*, which the defect-root modules prove directly by continuity of the
  functional calculus rather than by a modulus.
* **Missing: the quasicentral approximate unit (Lemma 8).**  Nothing in the
  repository mentions one.  The paper uses it to cut a lift `X` down to
  `X̃ = X(1 - i_λ)` with small commutators.  In corona vocabulary this step
  also disappears: a bounded representative of a corona class already has null
  commutators against anything the class commutes with, which is what
  `ShulmanFillCommutantUnitary.coronaUnitary_commutes_of_tendsto_commutator`
  records in the other direction.

So Lemma 9 is complete for the corona route and incomplete for the `𝒟` route,
and the two missing pieces are exactly the two quantitative devices —
Pedersen's inequality and the quasicentral unit — that the corona replaces by
null sequences.  The estimate below is likewise needed only on the `𝒟` route;
on the corona route the flip commutes exactly and the two families agree on
`C` on the nose.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter

noncomputable section

variable {M : Type} [CStarAlgebra M]

/-! ## Conjugation by a unitary is isometric -/

theorem norm_mul_unitary_right (x : M) (u : unitary M) :
    ‖x * (u : M)‖ = ‖x‖ := by
  have hcalc : (x * (u : M)) * star (x * (u : M)) = x * star x := by
    rw [star_mul, ← mul_assoc, mul_assoc x (u : M) (star (u : M)),
      Unitary.mul_star_self_of_mem u.2, mul_one]
  have hsq : ‖x * (u : M)‖ * ‖x * (u : M)‖ = ‖x‖ * ‖x‖ := by
    rw [← CStarRing.norm_self_mul_star, ← CStarRing.norm_self_mul_star, hcalc]
  nlinarith [norm_nonneg (x * (u : M)), norm_nonneg x, hsq]

theorem norm_unitary_mul_left (u : unitary M) (x : M) :
    ‖(u : M) * x‖ = ‖x‖ := by
  have hcalc : star ((u : M) * x) * ((u : M) * x) = star x * x := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (u : M)) (u : M) x,
      Unitary.star_mul_self_of_mem u.2, one_mul]
  have hsq : ‖(u : M) * x‖ * ‖(u : M) * x‖ = ‖x‖ * ‖x‖ := by
    rw [← CStarRing.norm_star_mul_self, ← CStarRing.norm_star_mul_self, hcalc]
  nlinarith [norm_nonneg ((u : M) * x), norm_nonneg x, hsq]

@[simp] theorem norm_unitaryConj (u : unitary M) (x : M) :
    ‖unitaryConj u x‖ = ‖x‖ := by
  -- `norm_mul_unitary_right _ (star u)` is stated at `↑(star u)`, which is
  -- `star ↑u` only up to unfolding the coercion, so the goal is put in that form.
  have hcoe : ((star u : unitary M) : M) = star (u : M) := Unitary.coe_star
  show ‖(u : M) * x * star (u : M)‖ = ‖x‖
  rw [← hcoe, norm_mul_unitary_right ((u : M) * x) (star u),
    norm_unitary_mul_left u x]

/-- The displacement under conjugation is the commutator, exactly. -/
theorem norm_unitaryConj_sub_self (u : unitary M) (a : M) :
    ‖unitaryConj u a - a‖ = ‖(u : M) * a - a * (u : M)‖ := by
  have hfac : (u : M) * a * star (u : M) - a =
      ((u : M) * a - a * (u : M)) * star (u : M) := by
    rw [sub_mul, mul_assoc a (u : M) (star (u : M)),
      Unitary.mul_star_self_of_mem u.2, mul_one]
  have hcoe : ((star u : unitary M) : M) = star (u : M) := Unitary.coe_star
  show ‖(u : M) * a * star (u : M) - a‖ = ‖(u : M) * a - a * (u : M)‖
  rw [hfac, ← hcoe, norm_mul_unitary_right _ (star u)]

/-! ## The estimate on page 8 -/

private theorem lt_of_dist_zero_lt {x r : ℝ} (hx : 0 ≤ x) (h : dist x 0 < r) :
    x < r := by
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hx] at h

private theorem dist_zero_lt_of_lt {x r : ℝ} (hx : 0 ≤ x) (h : x < r) :
    dist x 0 < r := by
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg hx]

/-- **Shulman's page 8 estimate.**  Contractive, asymptotically subtractive
families whose commutators against a sequence of unitaries die at every member
of a dense sequence agree asymptotically after conjugation, at every element.

Only three properties of the families are used: contractivity, asymptotic
compatibility with subtraction, and the commutator hypothesis.  Nothing about
where they take their values, and nothing about `𝒟`. -/
theorem tendsto_norm_unitaryConj_sub {C : Type} [CStarAlgebra C]
    (phi : ℕ → C → M) (V : ℕ → unitary M) (a : ℕ → C) (ha : DenseRange a)
    (hcontract : ∀ k x, ‖phi k x‖ ≤ ‖x‖)
    (hsub : ∀ x y : C,
      Tendsto (fun k ↦ ‖phi k (x - y) - (phi k x - phi k y)‖) atTop (nhds 0))
    (hcomm : ∀ j : ℕ, Tendsto
      (fun k ↦ ‖(V k : M) * phi k (a j) - phi k (a j) * (V k : M)‖)
      atTop (nhds 0))
    (c : C) :
    Tendsto (fun k ↦ ‖unitaryConj (V k) (phi k c) - phi k c‖) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨j, hj⟩ : ∃ j, ‖c - a j‖ < ε / 8 := by
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp ha c (ε / 8) (by positivity)
    exact ⟨j, by rwa [dist_eq_norm] at hj⟩
  obtain ⟨N₁, hN₁⟩ :=
    Metric.tendsto_atTop.mp (hsub c (a j)) (ε / 8) (by positivity)
  obtain ⟨N₂, hN₂⟩ :=
    Metric.tendsto_atTop.mp (hcomm j) (ε / 8) (by positivity)
  refine ⟨max N₁ N₂, fun k hk ↦ ?_⟩
  have hdefect : ‖phi k (c - a j) - (phi k c - phi k (a j))‖ < ε / 8 :=
    lt_of_dist_zero_lt (norm_nonneg _) (hN₁ k (le_of_max_le_left hk))
  have hcommk : ‖(V k : M) * phi k (a j) - phi k (a j) * (V k : M)‖ < ε / 8 :=
    lt_of_dist_zero_lt (norm_nonneg _) (hN₂ k (le_of_max_le_right hk))
  have hclose : ‖phi k c - phi k (a j)‖ < ε / 4 := by
    have htri : ‖phi k c - phi k (a j)‖ ≤
        ‖phi k (c - a j)‖ +
          ‖phi k (c - a j) - (phi k c - phi k (a j))‖ := by
      -- rewriting the goal by `hrw` would also hit the copy of
      -- `phi k c - phi k (a j)` inside the right-hand side, so the triangle
      -- inequality is rewritten instead.
      have h := norm_sub_le (phi k (c - a j))
        (phi k (c - a j) - (phi k c - phi k (a j)))
      have hrw : phi k (c - a j) - (phi k (c - a j) - (phi k c - phi k (a j)))
          = phi k c - phi k (a j) := by abel
      rwa [hrw] at h
    have hbound : ‖phi k (c - a j)‖ ≤ ‖c - a j‖ := hcontract k (c - a j)
    linarith
  have hsplit : ‖unitaryConj (V k) (phi k c) - phi k c‖ ≤
      ‖phi k c - phi k (a j)‖ +
        ‖unitaryConj (V k) (phi k (a j)) - phi k (a j)‖ +
          ‖phi k (a j) - phi k c‖ := by
    have hrw : unitaryConj (V k) (phi k c) - phi k c =
        (unitaryConj (V k) (phi k c) - unitaryConj (V k) (phi k (a j))) +
          (unitaryConj (V k) (phi k (a j)) - phi k (a j)) +
            (phi k (a j) - phi k c) := by
      abel
    have hfirst : ‖unitaryConj (V k) (phi k c) -
        unitaryConj (V k) (phi k (a j))‖ = ‖phi k c - phi k (a j)‖ := by
      rw [← map_sub, norm_unitaryConj]
    calc ‖unitaryConj (V k) (phi k c) - phi k c‖
        ≤ ‖(unitaryConj (V k) (phi k c) - unitaryConj (V k) (phi k (a j))) +
            (unitaryConj (V k) (phi k (a j)) - phi k (a j))‖ +
              ‖phi k (a j) - phi k c‖ := by
          rw [hrw]
          exact norm_add_le _ _
      _ ≤ ‖unitaryConj (V k) (phi k c) -
              unitaryConj (V k) (phi k (a j))‖ +
            ‖unitaryConj (V k) (phi k (a j)) - phi k (a j)‖ +
              ‖phi k (a j) - phi k c‖ := by
          have := norm_add_le
            (unitaryConj (V k) (phi k c) - unitaryConj (V k) (phi k (a j)))
            (unitaryConj (V k) (phi k (a j)) - phi k (a j))
          linarith
      _ = ‖phi k c - phi k (a j)‖ +
            ‖unitaryConj (V k) (phi k (a j)) - phi k (a j)‖ +
              ‖phi k (a j) - phi k c‖ := by rw [hfirst]
  have hmiddle : ‖unitaryConj (V k) (phi k (a j)) - phi k (a j)‖ < ε / 8 := by
    rw [norm_unitaryConj_sub_self]
    exact hcommk
  have hrev : ‖phi k (a j) - phi k c‖ = ‖phi k c - phi k (a j)‖ :=
    norm_sub_rev _ _
  refine dist_zero_lt_of_lt (norm_nonneg _) ?_
  rw [hrev] at hsplit
  linarith

end

end ShulmanFill
end GroupApproximation
