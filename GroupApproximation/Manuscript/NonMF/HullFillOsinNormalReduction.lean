import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# Osin's Lemma 7.1 for a normal subgroup, reduced to three facts about
elementary closures

`Manuscript.NonMF.TheoremCDebts.osinLemma71` is the remaining Osin debt, in the
case `lem:saturation` uses it:

> `G` torsion-free with Hull's generating set `A`, `N ⊴ G` with `N ∩ gNg⁻¹`
> infinite for every `g` — then `N` acts non-elementarily on `Γ(G,A)`.

This module proves that statement from three facts about a single acylindrical
action, each of which is a statement about the elementary closure `E(g)` of a
loxodromic element and none of which mentions `N`:

* `LoxodromicOfCommute` — an element of infinite order commuting with a
  loxodromic element is loxodromic.  `E(g)` is virtually cyclic and contains the
  centralizer of `g`, so every infinite-order element of that centralizer moves
  the basepoint linearly.
* `ExistsIndependentConjugate` — if the whole group acts non-elementarily, then
  for every loxodromic `q` there is `a` with `q` and `a q a⁻¹` independent.
  `E(q)` is a proper subgroup, and a conjugator taken outside it moves the pair
  of endpoints of the axis of `q` off itself.
* `AxisDichotomy` — for a loxodromic `g` and any `c`, either `g` and
  `c g⁻¹ c⁻¹` are independent, or `c` commensurates the axis of `g`:
  `c gᵐ c⁻¹ = gⁿ` with `m, n ≠ 0`.  This is the "common-axis theorem" that
  `Sofic.HullSuitabilityGeometry` names as missing in the docstrings of
  `exists_loxodromic_mem_of_common_zpow` and
  `exists_escaping_or_noncommuting_of_isSNormal`.

Everything else is bookkeeping with the landed geometry, and it is what this
module supplies: `exists_loxodromic_mem_of_isSNormal` produces one loxodromic
element inside `N`, and `actsNonElementarily_of_isSNormal` turns one into the
two independent ones non-elementarity asks for, through
`HullGeometry.actsNonElementarily_of_normal_conjugate`.

## The three branches of the s-normal argument

`s`-normality gives, for the ambient loxodromic `g`, a `c ≠ 1` with `c ∈ N` and
`g c g⁻¹ ∈ N`.  `AxisDichotomy` splits on `c`:

* independent axes — `HullGeometry.exists_loxodromic_commutator_of_independent_conjugate`
  ping-pongs `gᴺ c g⁻ᴺ c⁻¹` into a loxodromic element of `N`;
* `c gᵐ c⁻¹ = gⁿ` with `m ≠ n` —
  `HullGeometry.exists_loxodromic_mem_of_conj_zpow_eq_zpow_of_ne` puts
  `g ^ (n - m)` in `N`;
* `c gᵐ c⁻¹ = gᵐ` — then `c` commutes with the loxodromic `gᵐ`, and `c` has
  infinite order because `G` is torsion-free, so `LoxodromicOfCommute` makes `c`
  itself loxodromic.

Acylindricity is not a hypothesis of anything below: it enters only through the
three facts above, which is where it belongs.

`s`-normality is used once, and weakly: `exists_ne_one_mem_conj` takes from it a
single `c ∈ N` with `c ≠ 1`.  For a normal `N` that is `N ≠ ⊥`, which is how
`Saturation.isSNormal_of_torsionFree` produced the hypothesis in the first
place, so the normal case of Osin's lemma costs nothing beyond nontriviality
once the three facts are available.  The general `s`-normal case, where `N` is
not normal, needs more: the conjugate `g c g⁻¹ ∈ N` that
`exists_ne_one_mem_conj` also returns is what replaces normality there, and it
goes unused below.

## Superseded

`GGT.Elementary` now carries all of this, and more: `GGT/ElementaryOsinSNormal`
proves the three facts below in these exact shapes and does the **general**
`s`-normal case — `osinNonElementary_of_geometry`, which is
`HullInputsCorrected.osinNonElementary` verbatim modulo its inputs — where this
module does only the normal case.  `GGT/ElementaryFillCentralizer` and
`GGT/ElementaryFillConjugate` inhabit the first two facts, and
`GGT/ElementaryProperClosure` weakens what the second of them costs.  So this
module is kept as the record of the reduction, not as its implementation: it is
the first statement of the split between the elementary-closure facts and the
`s`-normal bookkeeping, and nothing imports it.

Two things in it are still worth reading.  `exists_ne_one_mem_conj` is the half
of `HullGeometry.exists_escaping_or_noncommuting_of_isSNormal` that keeps the
commuting witness, and the observation recorded above — that for a normal `N`
the `s`-normality hypothesis is spent only on "`N` contains an element other than
the identity" — is what makes the normal case cost nothing beyond nontriviality.

## Status

**Not compiled.**  Written while builds were frozen, and not in the root import
list for that reason.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace OsinNormalReduction

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The three facts about elementary closures -/

/-- **An infinite-order element commuting with a loxodromic is loxodromic.**
For an acylindrical action this is the statement that the centralizer of a
loxodromic element consists of loxodromic elements and torsion. -/
def LoxodromicOfCommute (G : Type u) [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (x : X) : Prop :=
  ∀ g c : G, IsLoxodromic g x → Commute c g → ¬ IsOfFinOrder c → IsLoxodromic c x

/-- **A loxodromic element has an independent conjugate**, as soon as the whole
group acts non-elementarily: a conjugator outside the elementary closure of `q`
moves the endpoints of its axis off themselves. -/
def ExistsIndependentConjugate (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ActsNonElementarily (⊤ : Subgroup G) x →
    ∀ q : G, IsLoxodromic q x → ∃ a : G, Independent q (a * q * a⁻¹) x

/-- **The common-axis dichotomy.**  Either the axes of `g` and `c g⁻¹ c⁻¹` are
independent, or `c` commensurates the axis of `g` and a power relation
`c gᵐ c⁻¹ = gⁿ` holds with both exponents nonzero. -/
def AxisDichotomy (G : Type u) [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (x : X) : Prop :=
  ∀ g c : G, IsLoxodromic g x →
    Independent g (c * g⁻¹ * c⁻¹) x ∨
      ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ c * g ^ m * c⁻¹ = g ^ n

/-! ## Two small facts -/

/-- The hyperbolicity constant of a nonempty space is nonnegative: the four-point
condition at four copies of one point reads `-δ ≤ 0`.  `HullGeneratingSet` does
not carry this, and the ping-pong lemma needs it. -/
theorem nonneg_of_isHyperbolicSpace {X : Type v} [PseudoMetricSpace X] {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (x : X) : 0 ≤ δ := by
  have h := hδ x x x x
  have h0 : gromovProduct x x x = (0 : ℝ) := by simp
  rw [h0, min_self] at h
  linarith

/-- **`s`-normality, in the form the argument consumes**: the twisted
intersection is infinite, so it contains an element other than the identity.
This is the first half of the proof of
`HullGeometry.exists_escaping_or_noncommuting_of_isSNormal`, kept apart from the
commuting/noncommuting split so that the commuting witness survives. -/
theorem exists_ne_one_mem_conj {G : Type u} [Group G] {S : Subgroup G}
    (hS : HullSuitable.IsSNormal S) (g : G) :
    ∃ c ∈ S, c ≠ 1 ∧ g * c * g⁻¹ ∈ S := by
  have hinter := hS g
  by_contra hnone
  refine hinter (Set.Finite.subset (Set.finite_singleton (1 : G)) ?_)
  intro c hc
  obtain ⟨hcS, hgcS⟩ := hc
  have hc1 : c = 1 := by
    by_contra hc1
    exact hnone ⟨c, hcS, hc1, hgcS⟩
  simp [hc1]

/-! ## One loxodromic element inside the subgroup -/

/-- **The three branches, assembled.**  An `s`-normal normal subgroup of a
torsion-free group contains a loxodromic element, given the common-axis
dichotomy and the centralizer fact. -/
theorem exists_loxodromic_mem_of_isSNormal {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X)
    (htf : IsPowerTorsionFree G) {x : X}
    (hEC1 : LoxodromicOfCommute G x) (hEC3 : AxisDichotomy G x)
    {g : G} (hg : IsLoxodromic g x) {N : Subgroup G} [N.Normal]
    (hsn : HullSuitable.IsSNormal N) :
    ∃ q ∈ N, IsLoxodromic q x := by
  obtain ⟨c, hcN, hc1, -⟩ := exists_ne_one_mem_conj hsn g
  have hcinf : ¬ IsOfFinOrder c := htf.not_isOfFinOrder hc1
  rcases hEC3 g c hg with hind | ⟨m, n, hm, _hn, hpow⟩
  · obtain ⟨k, hmem, hlox⟩ :=
      exists_loxodromic_commutator_of_independent_conjugate hδ hδ0 hiso hcN hg hind
    exact ⟨_, hmem, hlox⟩
  · by_cases hmn : m = n
    · subst hmn
      have hcomm : Commute c (g ^ m) := by
        show c * g ^ m = g ^ m * c
        have hstep := congrArg (fun y : G => y * c) hpow
        simpa [mul_assoc] using hstep
      exact ⟨c, hcN, hEC1 (g ^ m) c (isLoxodromic_zpow hiso hg hm) hcomm hcinf⟩
    · exact exists_loxodromic_mem_of_conj_zpow_eq_zpow_of_ne hiso hcN hg hmn hpow

/-! ## Osin's Lemma 7.1 for a normal subgroup -/

/-- **Osin's Lemma 7.1, for a normal `s`-normal subgroup of a torsion-free
group**, from the three facts about elementary closures.  One loxodromic element
of `N` and one independent conjugate of it are what non-elementarity asks for,
and normality puts the conjugate back inside `N`. -/
theorem actsNonElementarily_of_isSNormal {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hiso : IsIsometricAction G X)
    (htf : IsPowerTorsionFree G) {x : X}
    (hEC1 : LoxodromicOfCommute G x) (hEC2 : ExistsIndependentConjugate G x)
    (hEC3 : AxisDichotomy G x)
    (hne : ActsNonElementarily (⊤ : Subgroup G) x)
    {N : Subgroup G} [N.Normal] (hsn : HullSuitable.IsSNormal N) :
    ActsNonElementarily N x := by
  obtain ⟨g, _, _, _, hg, _, _⟩ := id hne
  obtain ⟨q, hqN, hq⟩ :=
    exists_loxodromic_mem_of_isSNormal hδ hδ0 hiso htf hEC1 hEC3 hg hsn
  obtain ⟨a, hindA⟩ := hEC2 hne q hq
  exact actsNonElementarily_of_normal_conjugate hiso hqN hq hindA

/-! ## At Hull's Cayley graph -/

/-- The same, at `Γ(G,A)`: `HullGeneratingSet` supplies hyperbolicity, the
isometric action and the ambient non-elementarity, and
`nonneg_of_isHyperbolicSpace` supplies the sign of `δ`. -/
theorem osinLemma71_of_elementaryClosure {G : Type u} [Group G]
    (A : HullGeneratingSet G)
    (hEC1 : LoxodromicOfCommute G (Cayley.base A.alphabet))
    (hEC2 : ExistsIndependentConjugate G (Cayley.base A.alphabet))
    (hEC3 : AxisDichotomy G (Cayley.base A.alphabet))
    (hG : IsPowerTorsionFree G) (N : Subgroup G) [N.Normal]
    (hsn : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  actsNonElementarily_of_isSNormal A.hyperbolic
    (nonneg_of_isHyperbolicSpace A.hyperbolic (Cayley.base A.alphabet))
    A.isometric hG hEC1 hEC2 hEC3 A.nonElementary hsn

/-- **The debt `TheoremCDebts.osinLemma71`, reduced.**  What is left of Osin's
Lemma 7.1 in the case `lem:saturation` uses is exactly the three facts about
elementary closures, uniformly in the group and its Hull generating set. -/
theorem osinLemma71_of_elementaryClosureAll
    (hEC : ∀ {G : Type} [Group G] (A : HullGeneratingSet G),
      LoxodromicOfCommute G (Cayley.base A.alphabet) ∧
        ExistsIndependentConjugate G (Cayley.base A.alphabet) ∧
          AxisDichotomy G (Cayley.base A.alphabet)) :
    ∀ {G : Type} [Group G] (A : HullGeneratingSet G),
      IsPowerTorsionFree G → ∀ (N : Subgroup G) [N.Normal],
        HullSuitable.IsSNormal N →
          ActsNonElementarily N (Cayley.base A.alphabet) := by
  intro G _ A hG N _ hsn
  obtain ⟨h1, h2, h3⟩ := hEC A
  exact osinLemma71_of_elementaryClosure A h1 h2 h3 hG N hsn

end OsinNormalReduction
end NonMF
end Manuscript
end GroupApproximation
