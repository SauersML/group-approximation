import GroupApproximation.GGT.ElementaryCentralizerAxis

/-!
# Bowditch's dichotomy, reduced to one local estimate; and the normal case

Two things, both aimed at shrinking the residual list of `GGT.Elementary`.

## Bowditch's dichotomy is one bounded turn

`EscapingIsLoxodromic` --- under an acylindrical action on a hyperbolic space an
element whose orbit escapes every bounded set is loxodromic, so there are no
parabolics --- is Osin's Theorem 1.1 over Bowditch.  It does not have to be
carried as a citation, because the local-to-global half of it is already proved
in this repository.  `HullGeometry.isLoxodromic_of_local_backtracking` says that
one inequality suffices:

    2(C + δ) < d(x, p x)   and   (x | p² x)_{p x} ≤ C   ⟹   p loxodromic,

and `HullGeometry.isLoxodromic_of_pow_isLoxodromic` descends loxodromy from a
positive power to the element.  So the whole of Bowditch's theorem, for the uses
here, is the statement that an escaping element has **some** power whose orbit
turns by a bounded amount relative to its step length:

    EscapingBoundedTurn G δ x :
      ∀ c, IsEscaping c x → ∃ k > 0, ∃ C, 0 ≤ C + δ ∧
        2 * (C + δ) < dist x ((c ^ k) • x) ∧
        gromovProduct x (((c ^ k) ^ 2) • x) ((c ^ k) • x) ≤ C

`escapingIsLoxodromic_of_boundedTurn` is then three lines.

**This is where acylindricity enters, and it must.**  The estimate is false
without it: a parabolic isometry of the hyperbolic plane escapes every bounded
set, and every power of it has its turn `(x | p² x)_{p x}` comparable to
`d(x, p x) / 2`, so no `C` works.  Anyone discharging `EscapingBoundedTurn` is
therefore obliged to use `IsAcylindrical`, and a proof that does not is wrong.

## The normal case does not need the classification

`HasLoxodromicOfUnbounded` (Osin's Theorem 1.1 in its subgroup form) was carried
only to produce a loxodromic element inside the `s`-normal subgroup.  When `N` is
normal --- the only case `lem:saturation` uses --- it is not needed, because the
axis dichotomy produces one directly:

Take `c ∈ N`, `c ≠ 1`, and an ambient loxodromic `g`.  Either the axes of `g` and
`c g⁻¹ c⁻¹` diverge, and the ping-pong lemma
`HullGeometry.exists_loxodromic_commutator_of_independent_conjugate` puts a
loxodromic commutator in `N`; or `c gᵐ c⁻¹ = gⁿ` with `m, n ≠ 0`, and then either
`m ≠ n`, when `HullGeometry.exists_loxodromic_mem_of_conj_zpow_eq_zpow_of_ne`
puts the loxodromic `g^{n−m}` in `N`, or `m = n`, when `c` commutes with the
loxodromic `gᵐ` and has infinite order, so is loxodromic by Bowditch.

Normality is used exactly twice, in the two `HullGeometry` lemmas, and
torsion-freeness once, to give `c` infinite order.

So `actsNonElementarily_of_isSNormal_of_normal_of_torsionFree` has residuals
`CentralizerOrbitNearAxis`, `EscapingIsLoxodromic` and
`IndependentOfNoCommonZpow` only --- three, where the general `s`-normal
statement has four and the pre-torsion-free statement had five.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

section Input

/-- **Bowditch's dichotomy, localised.**  An escaping element has a power whose
orbit turns by a bounded amount relative to its step length.  Acylindricity is
what makes this true; see the module docstring. -/
def EscapingBoundedTurn (G : Type u) [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (δ : ℝ) (x : X) : Prop :=
  ∀ c : G, IsEscaping c x → ∃ (k : ℕ) (C : ℝ), 0 < k ∧ 0 ≤ C + δ ∧
    2 * (C + δ) < dist x ((c ^ k) • x) ∧
    gromovProduct x (((c ^ k) ^ 2) • x) ((c ^ k) • x) ≤ C

end Input

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## The hyperbolicity constant is nonnegative -/

/-- A hyperbolic space with a point has a nonnegative constant: the four-point
condition at four copies of that point reads `t - δ ≤ t`.  Recorded because
`HullGeneratingSet` carries the constant and the condition but not the sign, and
the ping-pong lemma below needs the sign. -/
theorem nonneg_of_isHyperbolicSpace {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (p : X) :
    0 ≤ δ := by
  have h := hδ p p p p
  rw [min_self] at h
  linarith

/-! ## Bowditch's dichotomy from the local estimate -/

/-- **Bowditch's dichotomy, from one bounded turn.**  The local backtracking
criterion makes the power loxodromic, and loxodromy descends from a positive
power. -/
theorem escapingIsLoxodromic_of_boundedTurn {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hiso : IsIsometricAction G X) {x : X} (hbt : EscapingBoundedTurn G δ x) :
    EscapingIsLoxodromic G x := by
  intro c hc
  obtain ⟨k, C, hk, hCδ, hgap, hturn⟩ := hbt c hc
  exact isLoxodromic_of_pow_isLoxodromic hiso hk
    (isLoxodromic_of_local_backtracking hδ hiso hCδ hgap hturn)

/-! ## A nontrivial element of an `s`-normal subgroup -/

/-- An `s`-normal subgroup is infinite, so it has a nontrivial element.  The
twisted intersection at `1` is the subgroup itself. -/
theorem exists_ne_one_mem_of_isSNormal {N : Subgroup G}
    (hN : HullSuitable.IsSNormal N) : ∃ c : G, c ∈ N ∧ c ≠ 1 := by
  by_contra hnone
  push_neg at hnone
  refine (infinite_twistedIntersection hN 1)
    (Set.Finite.subset (Set.finite_singleton (1 : G)) ?_)
  intro y hy
  rw [Set.mem_singleton_iff]
  exact hnone y (mem_twistedIntersection.mp hy).1

/-! ## A loxodromic element inside a normal `s`-normal subgroup -/

/-- **The classification is not needed when `N` is normal.**  The axis dichotomy
applied to an ambient loxodromic and a nontrivial element of `N` produces a
loxodromic element of `N` in each of its three branches. -/
theorem exists_loxodromic_mem_of_isSNormal_of_normal_of_torsionFree {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {x : X} (hbow : EscapingIsLoxodromic G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    {g : G} (hg : IsLoxodromic g x) {N : Subgroup G} [N.Normal]
    (hN : HullSuitable.IsSNormal N) :
    ∃ q ∈ N, IsLoxodromic q x := by
  have hδ0 : 0 ≤ δ := nonneg_of_isHyperbolicSpace hδ x
  obtain ⟨c, hcN, hc1⟩ := exists_ne_one_mem_of_isSNormal hN
  have hcfin : ¬ IsOfFinOrder c := htf.not_isOfFinOrder hc1
  rcases independent_conj_inv_or_conj_zpow hiso hindep g c hg with
    hind | ⟨m, n, hm, hn, hpow⟩
  · obtain ⟨K, hmem, hlox⟩ :=
      exists_loxodromic_commutator_of_independent_conjugate hδ hδ0 hiso hcN hg
        hind
    exact ⟨_, hmem, hlox⟩
  · by_cases hmn : m = n
    · rw [hmn] at hpow
      have hcomm : c * g ^ n = g ^ n * c := by
        calc c * g ^ n = c * g ^ n * c⁻¹ * c := by group
          _ = g ^ n * c := by rw [hpow]
      have hgn : IsLoxodromic (g ^ n) x := isLoxodromic_zpow hiso hg hn
      exact ⟨c, hcN, isLoxodromic_of_commute_of_escapingIsLoxodromic hiso hacy
        hbow (g ^ n) c hgn hcomm hcfin⟩
    · exact exists_loxodromic_mem_of_conj_zpow_eq_zpow_of_ne hiso hcN hg hmn hpow

/-! ## Osin's Lemma 7.1 from a loxodromic element already found -/

/-- **Steps three and four of Osin's Lemma 7.1**, separated from the production
of the loxodromic element so that the normal case and the general `s`-normal case
can share them.  `N` is not assumed normal here. -/
theorem actsNonElementarily_of_mem_of_isSNormal_of_torsionFree
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) (hbow : EscapingIsLoxodromic G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) {N : Subgroup G}
    (hN : HullSuitable.IsSNormal N) {g : G} (hgN : g ∈ N)
    (hg : IsLoxodromic g x) : ActsNonElementarily N x := by
  have hcen : NoIndependentPairInCentralizer G x :=
    noIndependentPairInCentralizer_of_orbitNearAxis hiso hacy hnear
  obtain ⟨h, hhN, hh⟩ : ∃ h : G, h ∈ N ∧ h ∉ elementaryClosure g := by
    by_contra hcon
    push_neg at hcon
    have hNle : N ≤ elementaryClosure g := by
      intro y hy
      exact hcon y hy
    obtain ⟨f, hf⟩ :=
      exists_notMem_elementaryClosure_of_centralizer hiso hcen hG hg
    have hkl : IsLoxodromic (f * g * f⁻¹) x := isLoxodromic_conj hiso hg
    have hindgk : Independent g (f * g * f⁻¹) x := by
      refine hindep g (f * g * f⁻¹) hg hkl ?_
      intro p r hp hr heq
      exact hf (mem_elementaryClosure_of_common_zpow_conj hp hr heq)
    have hTg : twistedIntersection N f⁻¹ ≤ elementaryClosure g := by
      intro y hy
      exact hNle (mem_twistedIntersection.mp hy).1
    have hTk : twistedIntersection N f⁻¹ ≤ elementaryClosure (f * g * f⁻¹) := by
      intro y hy
      refine mem_elementaryClosure_conj' (a := f) ?_
      have h2 := (mem_twistedIntersection.mp hy).2
      rw [inv_inv] at h2
      exact hNle h2
    exact not_infinite_le_inf_elementaryClosure_of_torsionFree hiso hacy hnear
      hbow htf hg hkl hindgk hTg hTk (infinite_twistedIntersection hN f⁻¹)
  exact actsNonElementarily_of_notMem_elementaryClosure hiso hindep hgN hhN hg hh

/-- **Osin's Lemma 7.1 for a normal `s`-normal subgroup over a torsion-free
ambient group.**  Three residuals: `CentralizerOrbitNearAxis`,
`EscapingIsLoxodromic`, `IndependentOfNoCommonZpow`.  Neither
`HasLoxodromicOfUnbounded` nor `ElementaryClosureVirtuallyCyclic` appears. -/
theorem actsNonElementarily_of_isSNormal_of_normal_of_torsionFree {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) (hbow : EscapingIsLoxodromic G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) {N : Subgroup G} [N.Normal]
    (hN : HullSuitable.IsSNormal N) : ActsNonElementarily N x := by
  obtain ⟨g₁, -, -, -, hg₁, -, -⟩ := id hG
  obtain ⟨g, hgN, hg⟩ :=
    exists_loxodromic_mem_of_isSNormal_of_normal_of_torsionFree hδ hiso hacy hbow
      hindep htf hg₁ hN
  exact actsNonElementarily_of_mem_of_isSNormal_of_torsionFree hiso hacy hnear
    hbow hindep htf hG hN hgN hg

end Action

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The manuscript's statement, in the case it uses.**  `lem:saturation`
applies Osin's Lemma 7.1 to a *normal* subgroup of a torsion-free acylindrically
hyperbolic group, and in that case the residuals are the three named above.
`HullGeneratingSet` supplies the hyperbolicity constant, and the sign of that
constant is `nonneg_of_isHyperbolicSpace` rather than a further field. -/
theorem osinNonElementary_of_torsionFree_normal {G : Type u} [Group G]
    (A : HullGeneratingSet G)
    (hnear : CentralizerOrbitNearAxis G (Cayley.base A.alphabet))
    (hbow : EscapingIsLoxodromic G (Cayley.base A.alphabet))
    (hindep : IndependentOfNoCommonZpow G (Cayley.base A.alphabet))
    (htf : IsPowerTorsionFree G) (N : Subgroup G) [N.Normal]
    (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  actsNonElementarily_of_isSNormal_of_normal_of_torsionFree A.hyperbolic
    A.isometric A.acylindrical hnear hbow hindep htf A.nonElementary hN

end Cayley

end Elementary
end GGT
end GroupApproximation
