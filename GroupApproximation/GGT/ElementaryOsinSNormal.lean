import GroupApproximation.GGT.ElementaryClosure
import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# Osin's Lemma 7.1: an `s`-normal subgroup acts non-elementarily

Osin, *Acylindrically hyperbolic groups*, Trans. AMS 368 (2016), Lemma 7.1: if a
group `G` acts acylindrically and non-elementarily on a hyperbolic space and
`N ≤ G` is `s`-normal --- `N ∩ gNg⁻¹` is infinite for every `g` --- then `N` acts
non-elementarily.  This is the geometric debt recorded as
`HullInputsCorrected.osinNonElementary` in
`Manuscript/NonMF/HullFillCorrectedInputs.lean` and as
`TorsionFree.HullInputs.osinNonElementary` in
`Manuscript/NonMF/HullSmallCancellation.lean`.

`GGT.ElementaryClosure` builds the elementary closure `E(g)` and everything about
it that is algebra or translation length.  This module isolates the two facts of
Osin's §6 that genuinely need stability of quasi-geodesics, states them as named
`Prop`s with their citations, and proves Lemma 7.1 against them together with one
fact of §1 that needs Bowditch's dichotomy.

## The three named inputs

* `HasLoxodromicOfUnbounded` --- **Osin, Theorem 1.1**: an acylindrical action of
  a group on a hyperbolic space is elliptic, or lineal, or non-elementary; so a
  subgroup with unbounded orbits contains a loxodromic element.  Over Bowditch's
  theorem that an acylindrical action has no parabolics.
* `IndependentOfNoCommonZpow` --- **Osin, Lemma 6.5 and Corollary 6.6**: two
  loxodromic elements of an acylindrical action that share a limit point have a
  common nonzero power; contrapositively, no common power makes the two power
  orbits independent.  This is the fact
  `Sofic/HullSuitabilityGeometry.lean` names as missing in the docstrings of
  `exists_loxodromic_mem_of_common_zpow` and
  `exists_escaping_or_noncommuting_of_isSNormal`, and its proof runs through the
  Morse lemma: `acylindrical_common_power_of_two_orbit_fellow_travel` is the
  finite pigeonhole that consumes it, and the missing step is transporting the
  geodesic fellow-travelling of
  `exists_long_fellow_geodesics_of_not_independent` onto the two orbits at two
  far-apart basepoints with an error independent of their separation.
* `ElementaryClosureVirtuallyCyclic` --- **Osin, Theorem 6.8**: `E(g)` is
  virtually cyclic for loxodromic `g`, in the form that is used: every infinite
  subgroup of `E(g)` contains a nonzero power of `g`.  (`⟨g⟩` has finite index in
  `E(g)`, so an infinite `K ≤ E(g)` meets `⟨g⟩` in an infinite subgroup of `ℤ`.)

`OsinElementaryTheory` bundles the three.

## The proof, and what is proved outright

Write `x` for the basepoint and let `N` be `s`-normal.

1. **`N` is not elliptic** --- `not_bddOrbit_of_isSNormal`, proved here with no
   input.  Suppose every `c ∈ N` moves `x` by at most `B`.  Take a loxodromic
   `g₁` of `G` and a power `M` with `d(x, g₁^M x) ≥ R(B+1)`.  `s`-normality at
   `g₁^{-M}` gives infinitely many `c` with `c ∈ N` and `g₁^{-M} c g₁^{M} ∈ N`.
   Each such `c` moves `x` by at most `B`, and moves `g₁^M x` by
   `d(x, g₁^{-M} c g₁^{M} x) ≤ B`.  Acylindricity bounds the number of such
   elements, so the infinite set embeds in a finite one.
2. **`N` contains a loxodromic `g`** --- step 1 and
   `HasLoxodromicOfUnbounded`.
3. **`N` is not contained in `E(g)`.**  Suppose it is.  The ambient action is
   non-elementary, so `E(g) ≠ G` (`exists_notMem_elementaryClosure`: if the two
   independent ambient loxodromics both lay in `E(g)`, virtual cyclicity would
   give them powers inside `⟨g⟩`, so a common power, so no independence).  Take
   `f ∉ E(g)` and put `k = f g f⁻¹`.  A common nonzero power of `g` and `k` is a
   witness for `f ∈ E(g)`, so there is none, and `IndependentOfNoCommonZpow`
   makes `g` and `k` independent.  The twisted intersection `T = N ∩ f N f⁻¹` is
   infinite by `s`-normality, lies in `E(g)` because `N` does, and lies in `E(k)`
   because `f⁻¹ T f ⊆ N ⊆ E(g)`.  Virtual cyclicity applied inside `E(g)` puts a
   power `gʲ` (`j ≠ 0`) into `T`, so into `E(k)`; virtual cyclicity applied
   inside `E(k)` to the infinite subgroup `⟨gʲ⟩` puts a power `kⁱ` (`i ≠ 0`) into
   `⟨gʲ⟩`.  That is a common nonzero power of `g` and `k`, which contradicts
   their independence.
4. **Two independent loxodromics in `N`** --- take `h ∈ N \ E(g)`.  Then
   `h g h⁻¹ ∈ N`, it is loxodromic, and it is independent from `g` because a
   common power of `g` and `h g h⁻¹` is a witness for `h ∈ E(g)`.  This is
   `actsNonElementarily_of_notMem_elementaryClosure`, and it needs no normality
   of `N` at all.

The core of step 3 is `not_infinite_le_inf_elementaryClosure`: a subgroup lying
in the elementary closures of two independent loxodromics is finite, which is the
usable form of "`E(g) ∩ E(k)` is finite".  A second corollary of virtual
cyclicity worth naming is
`exists_common_zpow_of_mem_elementaryClosure_of_torsionFree`: over a torsion-free
ambient group every nontrivial element of `E(g)` has a nonzero power in common
with `g`.  That is what replaces the false reading `E(g) = ⟨g⟩` --- a torsion-free
virtually cyclic group is infinite cyclic, so `E(g)` is generated by a root of
`g`, and equals `⟨g⟩` only when `g` has no root in it.

Step 4 is where the target statement comes from, and steps 1 and 3 are where
`s`-normality is spent.  Specialising to the Cayley graph of Hull's generating
set gives `osinNonElementary_of_geometry`, whose statement is the field
`HullInputsCorrected.osinNonElementary` verbatim.

## Three statements for the normal case

`Manuscript/NonMF/HullFillOsinNormalReduction.lean` reduces the *normal* case of
Lemma 7.1 to three facts about elementary closures.  All three are proved here
from the named inputs above, in exactly their shapes:
`isLoxodromic_of_commute_of_not_isOfFinOrder` (their `LoxodromicOfCommute`),
`exists_independent_conjugate` (their `ExistsIndependentConjugate`), and
`independent_conj_inv_or_conj_zpow` (their `AxisDichotomy`).  The first two need
`ElementaryClosureVirtuallyCyclic`, and the third needs only
`IndependentOfNoCommonZpow`.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The three literature inputs -/

/-- **Osin, *Acylindrically hyperbolic groups*, Theorem 1.1.**  For an
acylindrical action on a hyperbolic space, a subgroup whose orbit is unbounded
contains a loxodromic element.

Osin's Theorem 1.1 classifies acylindrical actions as elliptic, lineal, or
non-elementary, and the last two contain loxodromic elements; the ingredient
that is not elementary is Bowditch's theorem that an acylindrical action has no
parabolic elements. -/
def HasLoxodromicOfUnbounded (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ K : Subgroup G, (¬ ∃ B : ℝ, ∀ c ∈ K, dist x (c • x) ≤ B) →
    ∃ c ∈ K, IsLoxodromic c x

/-- **Osin, Lemma 6.5 and Corollary 6.6.**  Two loxodromic elements of an
acylindrical action with no common nonzero power have independent power orbits.

Equivalently: two loxodromics sharing a limit point at infinity generate a
virtually cyclic subgroup, so they have a common power.  The proof passes
through stability of quasi-geodesics; `Sofic/HullSuitabilityGeometry.lean` has
the fellow-travelling half (`exists_long_fellow_geodesics_of_not_independent`,
`dist_le_four_delta_of_le_gromovProduct`) and the finite pigeonhole that
consumes the conclusion (`acylindrical_common_power_of_two_orbit_fellow_travel`)
and stops between them at a logarithmic Morse bound. -/
def IndependentOfNoCommonZpow (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ a b : G, IsLoxodromic a x → IsLoxodromic b x →
    (∀ p q : ℤ, p ≠ 0 → q ≠ 0 → a ^ p ≠ b ^ q) → Independent a b x

/-- **Osin, Theorem 6.8.**  For a loxodromic `g` of an acylindrical action,
`E(g)` is virtually cyclic, in the form used below: `⟨g⟩` has finite index in
`E(g)`, so every infinite subgroup of `E(g)` meets `⟨g⟩` in an infinite subgroup
of `ℤ` and therefore contains a nonzero power of `g`. -/
def ElementaryClosureVirtuallyCyclic (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ g : G, IsLoxodromic g x → ∀ K : Subgroup G, K ≤ elementaryClosure g →
    ((K : Subgroup G) : Set G).Infinite → ∃ j : ℤ, j ≠ 0 ∧ g ^ j ∈ K

/-- The three facts of Osin's §1 and §6 that the argument below consumes. -/
structure OsinElementaryTheory (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop where
  /-- Osin, Theorem 1.1. -/
  loxodromicOfUnbounded : HasLoxodromicOfUnbounded G x
  /-- Osin, Lemma 6.5 and Corollary 6.6. -/
  independentOfNoCommonZpow : IndependentOfNoCommonZpow G x
  /-- Osin, Theorem 6.8. -/
  elementaryClosureVirtuallyCyclic : ElementaryClosureVirtuallyCyclic G x

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## An `s`-normal subgroup is not elliptic -/

/-- **The elliptic case is excluded, with no literature input.**

If every element of `N` moved `x` by at most `B`, then for a loxodromic `g` and
a large power `M` the infinitely many `c` with `c ∈ N` and
`g^{-M} c g^{M} ∈ N` would all move both `x` and `g^M x` by at most `B`, and
acylindricity allows only finitely many elements to do that once the two points
are far apart. -/
theorem not_bddOrbit_of_isSNormal (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {N : Subgroup G}
    (hN : HullSuitable.IsSNormal N) {g : G} {x : X} (hg : IsLoxodromic g x) :
    ¬ ∃ B : ℝ, ∀ c ∈ N, dist x (c • x) ≤ B := by
  rintro ⟨B, hB⟩
  have hBε : B ≤ |B| + 1 := by linarith [le_abs_self B]
  obtain ⟨R, N₀, hRN⟩ := hacy (|B| + 1) (by linarith [abs_nonneg B])
  have hev := hg.isEscaping.eventually_ge_atTop R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  have hfar : R ≤ dist x ((g ^ M) • x) := hM M le_rfl
  obtain ⟨hfinite, -⟩ := hRN x ((g ^ M) • x) hfar
  refine (hN ((g ^ M)⁻¹)) (Set.Finite.subset hfinite ?_)
  rintro c ⟨hcN, hcconj⟩
  have hmem : ((g ^ M)⁻¹ * c * (g ^ M)) ∈ N := by
    have h2 := hcconj
    rwa [inv_inv] at h2
  have hmove : dist ((g ^ M) • x) (c • ((g ^ M) • x))
      = dist x (((g ^ M)⁻¹ * c * (g ^ M)) • x) := by
    have h := hiso ((g ^ M)⁻¹) ((g ^ M) • x) (c • ((g ^ M) • x))
    have hl : ((g ^ M)⁻¹) • ((g ^ M) • x) = x := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    have hr : ((g ^ M)⁻¹) • (c • ((g ^ M) • x))
        = ((g ^ M)⁻¹ * c * (g ^ M)) • x := by
      rw [mul_smul, mul_smul]
    rw [hl, hr] at h
    exact h.symm
  refine ⟨le_trans (hB c hcN) hBε, ?_⟩
  rw [hmove]
  exact le_trans (hB _ hmem) hBε

/-! ## Outside the elementary closure, the conjugate is independent -/

/-- **The main geometric lemma, against its named input.**  An element outside
`E(g)` conjugates `g` to an independent loxodromic direction: a common nonzero
power of `g` and `h g h⁻¹` would be a witness for `h ∈ E(g)`. -/
theorem independent_conj_of_notMem_elementaryClosure
    (hiso : IsIsometricAction G X) {x : X}
    (hindep : IndependentOfNoCommonZpow G x) {g h : G}
    (hg : IsLoxodromic g x) (hh : h ∉ elementaryClosure g) :
    Independent g (h * g * h⁻¹) x := by
  refine hindep g (h * g * h⁻¹) hg (isLoxodromic_conj hiso hg) ?_
  intro p q hp hq heq
  exact hh (mem_elementaryClosure_of_common_zpow_conj hp hq heq)

/-- **Independence of `g` from its conjugate is exactly membership failing.**
The forward direction is `not_independent_conj_of_mem_elementaryClosure`, which
needs no input. -/
theorem independent_conj_iff_notMem_elementaryClosure
    (hiso : IsIsometricAction G X) {x : X}
    (hindep : IndependentOfNoCommonZpow G x) {g h : G}
    (hg : IsLoxodromic g x) :
    Independent g (h * g * h⁻¹) x ↔ h ∉ elementaryClosure g := by
  refine ⟨fun hind hmem => ?_,
    independent_conj_of_notMem_elementaryClosure hiso hindep hg⟩
  exact not_independent_conj_of_mem_elementaryClosure hiso hg hmem hind

/-- **A subgroup with a loxodromic element and an element outside its elementary
closure acts non-elementarily.**  The two independent loxodromics are `g` and its
conjugate by the outside element, and the conjugate lies in the subgroup because
both factors do.  No normality is used. -/
theorem actsNonElementarily_of_notMem_elementaryClosure
    (hiso : IsIsometricAction G X) {x : X}
    (hindep : IndependentOfNoCommonZpow G x) {S : Subgroup G} {g h : G}
    (hgS : g ∈ S) (hhS : h ∈ S) (hg : IsLoxodromic g x)
    (hh : h ∉ elementaryClosure g) :
    ActsNonElementarily S x := by
  refine ⟨g, hgS, h * g * h⁻¹, ?_, hg, isLoxodromic_conj hiso hg,
    independent_conj_of_notMem_elementaryClosure hiso hindep hg hh⟩
  exact S.mul_mem (S.mul_mem hhS hgS) (S.inv_mem hhS)

/-! ## The elementary closure is proper -/

/-- **`E(g)` is not everything.**  If both of the two independent ambient
loxodromics lay in `E(g)`, virtual cyclicity would put a nonzero power of `g`
inside each of their cyclic subgroups, so `g^{j₁} = a^{m₁}` and `g^{j₂} = b^{m₂}`
with all four exponents nonzero, so `a^{m₁j₂} = b^{m₂j₁}` --- a common nonzero
power, which independence forbids. -/
theorem exists_notMem_elementaryClosure (hiso : IsIsometricAction G X) {x : X}
    (hvc : ElementaryClosureVirtuallyCyclic G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) {g : G}
    (hg : IsLoxodromic g x) :
    ∃ f : G, f ∉ elementaryClosure g := by
  obtain ⟨a, -, b, -, ha, hb, hab⟩ := hG
  by_contra hall
  push Not at hall
  have hkey : ∀ c : G, IsLoxodromic c x →
      ∃ j m : ℤ, j ≠ 0 ∧ m ≠ 0 ∧ g ^ j = c ^ m := by
    intro c hc
    have hsub : Subgroup.zpowers c ≤ elementaryClosure g := by
      intro y _
      exact hall y
    obtain ⟨j, hj, hjmem⟩ :=
      hvc g hg (Subgroup.zpowers c) hsub (infinite_coe_zpowers hc)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hjmem
    refine ⟨j, m, hj, ?_, hm.symm⟩
    intro hm0
    rw [hm0, zpow_zero] at hm
    exact zpow_ne_one_of_isLoxodromic hg hj hm.symm
  obtain ⟨j₁, m₁, hj₁, hm₁, he₁⟩ := hkey a ha
  obtain ⟨j₂, m₂, hj₂, hm₂, he₂⟩ := hkey b hb
  have hcommon : a ^ (m₁ * j₂) = b ^ (m₂ * j₁) := by
    calc a ^ (m₁ * j₂) = (a ^ m₁) ^ j₂ := by rw [zpow_mul]
      _ = (g ^ j₁) ^ j₂ := by rw [← he₁]
      _ = g ^ (j₁ * j₂) := by rw [← zpow_mul]
      _ = g ^ (j₂ * j₁) := by rw [mul_comm j₁ j₂]
      _ = (g ^ j₂) ^ j₁ := by rw [zpow_mul]
      _ = (b ^ m₂) ^ j₁ := by rw [he₂]
      _ = b ^ (m₂ * j₁) := by rw [← zpow_mul]
  exact not_independent_of_common_zpow hiso ha (mul_ne_zero hm₁ hj₂)
    (mul_ne_zero hm₂ hj₁) hcommon hab

/-! ## Two independent elementary closures share no infinite subgroup -/

/-- **The usable form of "`E(g) ∩ E(k)` is finite".**  A subgroup lying in the
elementary closures of two independent loxodromics is finite: virtual cyclicity
inside `E(g)` puts a power `gʲ` into it, virtual cyclicity inside `E(k)` applied
to the infinite cyclic group `⟨gʲ⟩` puts a power `kⁱ` back into `⟨gʲ⟩`, and that
common nonzero power contradicts independence. -/
theorem not_infinite_le_inf_elementaryClosure (hiso : IsIsometricAction G X)
    {x : X} (hvc : ElementaryClosureVirtuallyCyclic G x) {g k : G}
    (hg : IsLoxodromic g x) (hk : IsLoxodromic k x)
    (hind : Independent g k x) {K : Subgroup G}
    (hKg : K ≤ elementaryClosure g) (hKk : K ≤ elementaryClosure k)
    (hKinf : ((K : Subgroup G) : Set G).Infinite) : False := by
  obtain ⟨j, hj, hjmem⟩ := hvc g hg K hKg hKinf
  have hgjlox : IsLoxodromic (g ^ j) x := isLoxodromic_zpow hiso hg hj
  obtain ⟨i, hi, himem⟩ := hvc k hk (Subgroup.zpowers (g ^ j))
    (Subgroup.zpowers_le.mpr (hKk hjmem)) (infinite_coe_zpowers hgjlox)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp himem
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zpow_zero] at hm
    exact zpow_ne_one_of_isLoxodromic hk hi hm.symm
  have hcommon : g ^ (j * m) = k ^ i := by
    rw [zpow_mul]
    exact hm
  exact not_independent_of_common_zpow hiso hg (mul_ne_zero hj hm0) hi
    hcommon hind

/-- **Over a torsion-free ambient group, `E(g)` is commensurable to `⟨g⟩`
elementwise.**  Every nontrivial element of `E(g)` has infinite order, so its
cyclic subgroup is an infinite subgroup of `E(g)` and contains a nonzero power
of `g`.

This replaces the false reading `E(g) = ⟨g⟩`: a torsion-free virtually cyclic
group is infinite cyclic, so `E(g)` is `⟨h⟩` for a root `h` of `g`, and equals
`⟨g⟩` only when `g` has no root in it. -/
theorem exists_common_zpow_of_mem_elementaryClosure_of_torsionFree
    {x : X} (hvc : ElementaryClosureVirtuallyCyclic G x)
    (htf : IsPowerTorsionFree G) {g c : G} (hg : IsLoxodromic g x)
    (hc : c ∈ elementaryClosure g) (hc1 : c ≠ 1) :
    ∃ i m : ℤ, i ≠ 0 ∧ m ≠ 0 ∧ g ^ i = c ^ m := by
  have hcinf : ¬ IsOfFinOrder c := htf.not_isOfFinOrder hc1
  have hle : Subgroup.zpowers c ≤ elementaryClosure g :=
    Subgroup.zpowers_le.mpr hc
  have hinf : ((Subgroup.zpowers c : Subgroup G) : Set G).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun t : ℤ => c ^ t) ?_ ?_
    · exact injective_zpow_iff_not_isOfFinOrder.mpr hcinf
    · intro t
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) t
  obtain ⟨i, hi, himem⟩ := hvc g hg (Subgroup.zpowers c) hle hinf
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp himem
  refine ⟨i, m, hi, ?_, hm.symm⟩
  intro h0
  rw [h0, zpow_zero] at hm
  exact zpow_ne_one_of_isLoxodromic hg hi hm.symm

/-! ## Osin's Lemma 7.1 -/

/-- **Osin, Lemma 7.1.**  An `s`-normal subgroup of a group acting
acylindrically and non-elementarily on a hyperbolic space acts
non-elementarily. -/
theorem actsNonElementarily_of_isSNormal (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {x : X}
    (hlox : HasLoxodromicOfUnbounded G x)
    (hindep : IndependentOfNoCommonZpow G x)
    (hvc : ElementaryClosureVirtuallyCyclic G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x)
    {N : Subgroup G} (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N x := by
  obtain ⟨g₁, -, -, -, hg₁, -, -⟩ := id hG
  obtain ⟨g, hgN, hg⟩ :=
    hlox N (not_bddOrbit_of_isSNormal hiso hacy hN hg₁)
  obtain ⟨h, hhN, hh⟩ : ∃ h : G, h ∈ N ∧ h ∉ elementaryClosure g := by
    by_contra hcon
    push Not at hcon
    have hNle : N ≤ elementaryClosure g := by
      intro y hy
      exact hcon y hy
    obtain ⟨f, hf⟩ := exists_notMem_elementaryClosure hiso hvc hG hg
    have hk : IsLoxodromic (f * g * f⁻¹) x := isLoxodromic_conj hiso hg
    have hindgk : Independent g (f * g * f⁻¹) x := by
      refine hindep g (f * g * f⁻¹) hg hk ?_
      intro p q hp hq heq
      exact hf (mem_elementaryClosure_of_common_zpow_conj hp hq heq)
    have hTg : twistedIntersection N f⁻¹ ≤ elementaryClosure g := by
      intro y hy
      exact hNle (mem_twistedIntersection.mp hy).1
    have hTk : twistedIntersection N f⁻¹ ≤ elementaryClosure (f * g * f⁻¹) := by
      intro y hy
      refine mem_elementaryClosure_conj' (a := f) ?_
      have h2 := (mem_twistedIntersection.mp hy).2
      rw [inv_inv] at h2
      exact hNle h2
    exact not_infinite_le_inf_elementaryClosure hiso hvc hg hk hindgk hTg hTk
      (infinite_twistedIntersection hN f⁻¹)
  exact actsNonElementarily_of_notMem_elementaryClosure hiso hindep hgN hhN hg hh

/-- Osin's Lemma 7.1 from the bundled inputs. -/
theorem actsNonElementarily_of_isSNormal_of_theory
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hOsin : OsinElementaryTheory G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x)
    {N : Subgroup G} (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N x :=
  actsNonElementarily_of_isSNormal hiso hacy hOsin.loxodromicOfUnbounded
    hOsin.independentOfNoCommonZpow hOsin.elementaryClosureVirtuallyCyclic hG hN

/-! ## The three statements consumed by the normal-subgroup reduction

`Manuscript/NonMF/HullFillOsinNormalReduction.lean` states these three as named
`Prop`s (`LoxodromicOfCommute`, `ExistsIndependentConjugate`, `AxisDichotomy`)
and reduces the normal case of Lemma 7.1 to them.  All three are theorems here. -/

/-- **An infinite-order element commuting with a loxodromic is loxodromic.**  It
lies in `E(g)` because it commutes with `g`, and its cyclic subgroup is an
infinite subgroup of `E(g)`, so virtual cyclicity puts a nonzero power of `g`
inside it.  A common nonzero power transports loxodromy. -/
theorem isLoxodromic_of_commute_of_not_isOfFinOrder
    (hiso : IsIsometricAction G X) {x : X}
    (hvc : ElementaryClosureVirtuallyCyclic G x) (g c : G)
    (hg : IsLoxodromic g x) (hc : Commute c g) (hfin : ¬ IsOfFinOrder c) :
    IsLoxodromic c x := by
  have hle : Subgroup.zpowers c ≤ elementaryClosure g :=
    Subgroup.zpowers_le.mpr (mem_elementaryClosure_of_commute hc)
  have hinf : ((Subgroup.zpowers c : Subgroup G) : Set G).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => c ^ k) ?_ ?_
    · exact injective_zpow_iff_not_isOfFinOrder.mpr hfin
    · intro k
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  obtain ⟨j, hj, hjmem⟩ := hvc g hg (Subgroup.zpowers c) hle hinf
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hjmem
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zpow_zero] at hm
    exact zpow_ne_one_of_isLoxodromic hg hj hm.symm
  exact isLoxodromic_of_common_zpow hiso hg hj hm0 hm.symm

/-- **Every loxodromic has an independent conjugate**, once the ambient action is
non-elementary: the conjugator is any element outside the elementary closure,
which exists because the closure is proper. -/
theorem exists_independent_conjugate (hiso : IsIsometricAction G X) {x : X}
    (hindep : IndependentOfNoCommonZpow G x)
    (hvc : ElementaryClosureVirtuallyCyclic G x)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) (q : G)
    (hq : IsLoxodromic q x) :
    ∃ a : G, Independent q (a * q * a⁻¹) x := by
  obtain ⟨f, hf⟩ := exists_notMem_elementaryClosure hiso hvc hG hq
  exact ⟨f, independent_conj_of_notMem_elementaryClosure hiso hindep hq hf⟩

/-- **The axis dichotomy.**  For any `c`, either the axes of `g` and
`c g⁻¹ c⁻¹` diverge, or `c` conjugates a nonzero power of `g` to a nonzero power
of `g`.  The second alternative is membership in `E(g)` written out, so the
dichotomy is the excluded middle on that membership together with the
independence input. -/
theorem independent_conj_inv_or_conj_zpow (hiso : IsIsometricAction G X) {x : X}
    (hindep : IndependentOfNoCommonZpow G x) (g c : G)
    (hg : IsLoxodromic g x) :
    Independent g (c * g⁻¹ * c⁻¹) x ∨
      ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ c * g ^ m * c⁻¹ = g ^ n := by
  by_cases hc : c ∈ elementaryClosure g
  · obtain ⟨m, n, hm, hn, heq⟩ := mem_elementaryClosure.mp hc
    exact Or.inr ⟨m, n, hm, hn, heq⟩
  · left
    have hlox : IsLoxodromic (c * g⁻¹ * c⁻¹) x :=
      isLoxodromic_conj hiso (isLoxodromic_inv hiso hg)
    refine hindep g (c * g⁻¹ * c⁻¹) hg hlox ?_
    intro p r hp hr heq
    exact hc (mem_elementaryClosure_of_common_zpow_conj_inv hp hr heq)

end Action

/-! ## The manuscript's statement, at `Γ(G,A)` -/

/-- **Osin's Lemma 7.1 at Hull's Cayley graph.**  This is the statement of the
field `HullInputsCorrected.osinNonElementary`, and of
`TorsionFree.HullInputs.osinNonElementary`, proved from the three cited facts of
Osin's §1 and §6.  Hyperbolicity, acylindricity and ambient non-elementarity are
the fields `A` already carries, and the isometry clause is a theorem about the
word metric rather than a hypothesis. -/
theorem osinNonElementary_of_geometry {G : Type u} [Group G]
    (A : HullGeneratingSet G)
    (hlox : HasLoxodromicOfUnbounded G (Cayley.base A.alphabet))
    (hindep : IndependentOfNoCommonZpow G (Cayley.base A.alphabet))
    (hvc : ElementaryClosureVirtuallyCyclic G (Cayley.base A.alphabet))
    (N : Subgroup G) (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  actsNonElementarily_of_isSNormal A.isometric A.acylindrical hlox hindep hvc
    A.nonElementary hN

/-- The same from the bundled inputs. -/
theorem osinNonElementary_of_theory {G : Type u} [Group G]
    (A : HullGeneratingSet G)
    (hOsin : OsinElementaryTheory G (Cayley.base A.alphabet))
    (N : Subgroup G) (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  osinNonElementary_of_geometry A hOsin.loxodromicOfUnbounded
    hOsin.independentOfNoCommonZpow hOsin.elementaryClosureVirtuallyCyclic N hN

/-- **The debt, reduced.**  What is left of
`HullInputsCorrected.osinNonElementary` is the three facts of Osin's §1 and §6,
uniformly in the group and its Hull generating set. -/
theorem osinNonElementary_of_theoryAll
    (hOsin : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G),
      OsinElementaryTheory G (Cayley.base A.alphabet)) :
    ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G),
      HullSuitable.IsSNormal N →
        ActsNonElementarily N (Cayley.base A.alphabet) := by
  intro G _ A N hN
  exact osinNonElementary_of_theory A (hOsin A) N hN

end Elementary
end GGT
end GroupApproximation
