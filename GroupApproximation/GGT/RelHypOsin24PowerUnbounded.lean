import GroupApproximation.GGT.RelHypOsin24BoundedPenetration
import GroupApproximation.GGT.DGOProposition433Finite

/-!
# The power-pigeonhole step

The proof of Osin's Theorem 1.10 (Theorem `10` in the fetched Memoirs source)
uses the following algebraic implication.  Once bounded relative powers have
been put in one fixed finite double coset `K h H_λ`, two powers with the same
left factor differ by a nonzero power lying in `H_λ`.  For a finite peripheral
family, Proposition 4.33(b) then forces the original element itself into
`H_λ`: otherwise the intersection `H_λ ∩ g⁻¹H_λg` is finite, while it contains
all powers of that nonzero power.  This file proves those two steps from the
landed labelled relative-geometry API.

The source-dependent step that turns a bounded relative-length subsequence of
powers into one fixed finite `K h H_λ` is not reintroduced as an unchecked
hypothesis.  The proved statements below are the strict smaller algebraic and
finite-slice consequences to which that source argument reduces.  The finite
slice itself is in `RelHypOsin24BoundedPenetration`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Failure of escape produces a bounded subsequence -/

/-- **Bounded subsequence form of non-escape.**  If a power orbit does not
escape a metric space, one fixed radius contains infinitely many positive
powers.  This is the filter-theoretic first half of Osin's bounded-relative-
length argument, with no relative geometry in the statement. -/
def BoundedPowerSubsequenceStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (X : Type v) (_ : PseudoMetricSpace X)
    (_ : MulAction G X) (g : G) (x : X),
    ¬ IsEscaping g x →
      ∃ R : ℝ, {n : ℕ | dist x ((g ^ n) • x) ≤ R}.Infinite

/-- A non-escaping orbit has a bounded subsequence, by negating the
`Filter.tendsto_atTop` definition and using finite sets of natural numbers
to contradict arbitrarily large witnesses. -/
theorem boundedPowerSubsequence_proved :
    BoundedPowerSubsequenceStatement.{u, v} := by
  intro G instG X instX instAct g x hnot
  letI : Group G := instG
  letI : PseudoMetricSpace X := instX
  letI : MulAction G X := instAct
  rw [IsEscaping, Filter.tendsto_atTop] at hnot
  push Not at hnot
  obtain ⟨R, hR⟩ := hnot
  rw [Filter.frequently_atTop] at hR
  refine ⟨R, ?_⟩
  intro hfinite
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  obtain ⟨n, hnN, hnR⟩ := hR (N + 1)
  have hnmem : n ∈ {n : ℕ | dist x ((g ^ n) • x) ≤ R} := by
    exact le_of_lt hnR
  have hnle : n ≤ N := hN hnmem
  omega

/-- Model test for the bounded-subsequence statement: the one-point orbit is
bounded by radius zero, so its whole power-index set is infinite. -/
theorem boundedPowerSubsequence_trivialModel :
    ∃ R : ℝ, {n : ℕ | dist (1 : PUnit) (((1 : PUnit) ^ n) • (1 : PUnit)) ≤ R}.Infinite := by
  refine ⟨0, ?_⟩
  have hset :
      {n : ℕ | dist (1 : PUnit) (((1 : PUnit) ^ n) • (1 : PUnit)) ≤ (0 : ℝ)} =
        Set.univ := by
    ext n
    simp
  rw [hset]
  exact Set.infinite_univ

/-! ## A fixed double-coset witness forces a peripheral power -/

/-- **Fixed-double-coset power witness.**  If infinitely many positive powers
of `g` have the form `k h z` with the same `k` and `z ∈ H`, then a nonzero
positive power of `g` lies in `H`.  This is the power-pigeonhole calculation in
Osin's Lemma 4.2-type argument. -/
def FixedPeripheralPowerWitnessStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (H : Subgroup G) (g k h : G)
    (S : Set ℕ),
    S.Infinite →
      (∀ n : ℕ, n ∈ S → ∃ z : G, z ∈ H ∧ g ^ n = k * h * z) →
        ∃ m : ℕ, 0 < m ∧ g ^ m ∈ H

/-- The fixed-double-coset calculation. -/
theorem fixedPeripheralPowerWitness_proved :
    FixedPeripheralPowerWitnessStatement.{u} := by
  intro G instG H g k h S hS hdecomp
  letI : Group G := instG
  obtain ⟨n₁, hn₁S, hn₁gt⟩ := Set.Infinite.exists_gt hS 0
  obtain ⟨n₂, hn₂S, hn₂gt⟩ := Set.Infinite.exists_gt hS n₁
  obtain ⟨z₁, hz₁H, hz₁⟩ := hdecomp n₁ hn₁S
  obtain ⟨z₂, hz₂H, hz₂⟩ := hdecomp n₂ hn₂S
  have hsum : n₁ + (n₂ - n₁) = n₂ := by omega
  have hpowdiff : g ^ (n₂ - n₁) = z₁⁻¹ * z₂ := by
    calc
      g ^ (n₂ - n₁) = (g ^ n₁)⁻¹ * (g ^ n₁ * g ^ (n₂ - n₁)) := by group
      _ = (g ^ n₁)⁻¹ * g ^ (n₁ + (n₂ - n₁)) := by rw [pow_add]
      _ = (g ^ n₁)⁻¹ * g ^ n₂ := by rw [hsum]
      _ = (k * h * z₁)⁻¹ * (k * h * z₂) := by rw [hz₁, hz₂]
      _ = z₁⁻¹ * z₂ := by group
  refine ⟨n₂ - n₁, by omega, ?_⟩
  rw [hpowdiff]
  exact H.mul_mem (H.inv_mem hz₁H) hz₂H

/-- Model test for the pigeonhole calculation: in the one-point group the
peripheral subgroup is `⊤`, so the conclusion is immediate for `S = univ`. -/
theorem fixedPeripheralPowerWitness_trivialModel
    (S : Set ℕ) (_hS : S.Infinite) :
    ∃ m : ℕ, 0 < m ∧ (1 : PUnit) ^ m ∈ (⊤ : Subgroup PUnit) := by
  exact ⟨1, by omega, Subgroup.mem_top _⟩

/-! ## Hyperbolic elements have no peripheral powers -/

/-- **No peripheral power for a hyperbolic element.**  In a finite labelled
family, local finiteness and Proposition 4.33(b) imply that an infinite-order
element which is not parabolic has no positive power in any peripheral
subgroup.  The proof uses only the existing finite-family almost-malnormality
theorem and commutation of powers. -/
theorem no_peripheral_power_of_hyperbolic_finiteFamily
    {G : Type u} [Group G] {I : Type v} [Finite I]
    (D : RelGenSet G I) (hemb : D.IsHyperbolicallyEmbedded) {g : G}
    (hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    ∀ (lam : I) (m : ℕ), 0 < m → g ^ m ∉ D.fam lam := by
  have hnotfin : ¬ IsOfFinOrder g := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    exact hord n hn hpow
  have hinj : Function.Injective (fun n : ℕ => g ^ n) :=
    HullSCUnionGeometry.injective_pow_of_not_isOfFinOrder hnotfin
  intro lam m hm hmem
  have hgH : g ∈ D.fam lam := by
    by_contra hgnot
    have hfin :
        {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam lam}.Finite :=
      finite_conj_inter_of_notMem D hemb hgnot
    have hmul_inj : Function.Injective (fun n : ℕ => g ^ (m * n)) := by
      intro a b hab
      have hmul : m * a = m * b := hinj hab
      exact Nat.mul_left_cancel hm hmul
    have hpow_range : (Set.range (fun n : ℕ => g ^ (m * n))).Infinite :=
      Set.infinite_range_of_injective hmul_inj
    have hsubset :
        Set.range (fun n : ℕ => g ^ (m * n)) ⊆
          {x : G | x ∈ D.fam lam ∧ g⁻¹ * x * g ∈ D.fam lam} := by
      rintro x ⟨n, rfl⟩
      have hpown : g ^ (m * n) ∈ D.fam lam := by
        rw [pow_mul g m n]
        exact (D.fam lam).pow_mem hmem n
      constructor
      · exact hpown
      · have hcomm : Commute g (g ^ (m * n)) :=
          (Commute.refl g).pow_right _
        have hconj : g⁻¹ * g ^ (m * n) * g = g ^ (m * n) := by
          calc
            g⁻¹ * g ^ (m * n) * g = g⁻¹ * (g ^ (m * n) * g) := by
              rw [mul_assoc]
            _ = g⁻¹ * (g * g ^ (m * n)) := by
              rw [hcomm.eq]
            _ = g ^ (m * n) := by group
        rw [hconj]
        exact hpown
    have hfiniteRange :
        (Set.range (fun n : ℕ => g ^ (m * n))).Finite :=
      hfin.subset hsubset
    exact (Set.not_infinite.2 hfiniteRange) hpow_range
  exact hhyper ⟨lam, 1, by simpa using hgH⟩

/-- Model test for the no-peripheral-power theorem: in `PUnit` the order
hypothesis is impossible, so the theorem closes by contradiction. -/
theorem no_peripheral_power_of_hyperbolic_trivialModel
    {I : Type v} [Finite I] (D : RelGenSet PUnit I)
    (_hemb : D.IsHyperbolicallyEmbedded) (g : PUnit)
    (_hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    ∀ (lam : I) (m : ℕ), 0 < m → g ^ m ∉ D.fam lam := by
  intro lam m hm
  exfalso
  exact hord m hm (Subsingleton.elim _ _)

/-! ## The source-facing finite-slice contradiction -/

/-- **Fixed bounded-penetration slices contradict hyperbolicity.**  This is the
source-facing output of the two proved steps above.  Once a bounded power
subsequence has been placed in a fixed right peripheral ball and fixed left
factor, the hyperbolic infinite-order hypotheses are inconsistent. -/
theorem not_fixed_boundedPenetration_power_slice
    {G : Type u} [Group G] {I : Type v} [Finite I]
    (D : RelGenSet G I) (hemb : D.IsHyperbolicallyEmbedded) {g : G}
    (hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (lam : I) (n : ℕ) (k h : G) (S : Set ℕ) (hS : S.Infinite)
    (hdecomp : ∀ q : ℕ, q ∈ S →
      ∃ z : G, z ∈ D.relBall lam n ∧ g ^ q = k * h * z) :
    False := by
  have hfixed : ∀ q : ℕ, q ∈ S →
      ∃ z : G, z ∈ D.fam lam ∧ g ^ q = k * h * z := by
    intro q hq
    obtain ⟨z, hzball, hz⟩ := hdecomp q hq
    exact ⟨z, (RelGenSet.mem_relBall.mp hzball).1, hz⟩
  obtain ⟨m, hm, hmp⟩ := fixedPeripheralPowerWitness_proved G inferInstance
    (D.fam lam) g k h S hS hfixed
  exact no_peripheral_power_of_hyperbolic_finiteFamily D hemb hhyper hord lam m hm hmp

/-- Model test for the source-facing contradiction: the order premise is
impossible in `PUnit`, so every putative bounded slice is contradictory. -/
theorem not_fixed_boundedPenetration_power_slice_trivialModel
    {I : Type v} [Finite I] (D : RelGenSet PUnit I)
    (_hemb : D.IsHyperbolicallyEmbedded) (g : PUnit)
    (_hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    False := by
  exact hord 1 (by omega) (Subsingleton.elim _ _)

/-! ## Assembly once the source extraction estimate is supplied -/

/-- **Escape from Osin's bounded-penetration extraction.**  Suppose every
bounded subsequence of the relative power orbit can be placed in one fixed
finite double-coset slice with a bounded right peripheral factor.  The
bounded-subsequence lemma and the fixed-slice contradiction then prove
`IsEscaping`.  The displayed extraction hypothesis is exactly the geometric
step left in Osin's Lemma 4.2-type argument; it is stronger than the finite
slice theorem above and weaker than the final escape statement. -/
theorem isEscaping_of_boundedPenetration_extraction
    {G : Type u} [Group G] {I : Type v} [Finite I]
    (D : RelGenSet G I) (_hbase : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) {g : G}
    (hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (hExtract : ∀ (R : ℝ) (S : Set ℕ), S.Infinite →
      (∀ q : ℕ, q ∈ S →
        dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) ≤ R) →
      ∃ (lam : I) (n : ℕ) (k h : G),
        ∀ q : ℕ, q ∈ S →
          ∃ z : G, z ∈ D.relBall lam n ∧ g ^ q = k * h * z) :
    IsEscaping g (Cayley.base D.alphabet) := by
  classical
  by_contra hnot
  obtain ⟨R, hSraw⟩ := boundedPowerSubsequence_proved
    G inferInstance (Cayley.base D.alphabet) inferInstance inferInstance g
      (Cayley.base D.alphabet) hnot
  let S : Set ℕ :=
    {q : ℕ | dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) ≤ R}
  have hS : S.Infinite := by
    simpa [S] using hSraw
  obtain ⟨lam, n, k, h, hdecomp⟩ := hExtract R S hS (by
    intro q hq
    exact hq)
  exact not_fixed_boundedPenetration_power_slice D hemb hhyper hord lam n k h S hS
    hdecomp

/-/ Model test for the extraction assembly: the order premise is impossible in
`PUnit`, so the conclusion closes regardless of the supplied extraction map. -/
theorem isEscaping_of_boundedPenetration_extraction_trivialModel
    {I : Type v} [Finite I] (D : RelGenSet PUnit I)
    (_hbase : D.base.Finite) (_hemb : D.IsHyperbolicallyEmbedded) (g : PUnit)
    (_hhyper : IsHyperbolicElement D.fam g)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1)
    (_hExtract : ∀ (R : ℝ) (S : Set ℕ), S.Infinite →
      (∀ q : ℕ, q ∈ S →
        dist (Cayley.base D.alphabet) ((g ^ q) • Cayley.base D.alphabet) ≤ R) →
      ∃ (lam : I) (n : ℕ) (k h : PUnit),
        ∀ q : ℕ, q ∈ S →
          ∃ z : PUnit, z ∈ D.relBall lam n ∧ g ^ q = k * h * z) :
    IsEscaping g (Cayley.base D.alphabet) := by
  exfalso
  exact hord 1 (by omega) (Subsingleton.elim _ _)

end RelHyp
end GGT
end GroupApproximation
