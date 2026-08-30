import GroupApproximation.GGT.HullSCConeOffHeavyChordChain
import GroupApproximation.GGT.HullSCConeOffHeavyHyperbolic
import GroupApproximation.GGT.HullSCConeOffHeavyQuasiGeodesic

/-!
# The cyclic subgroup of a loxodromic element is quasiconvex

This module closes the chain that
`GGT/HullSCConeOffHeavyHyperbolic.lean` opened.  Clause (a) of the cone-off leaf
— hyperbolicity of `Γ(G, A ⊔ ⨆K)` — was reduced there to `IsWordQuasiconvex`,
and `IsWordQuasiconvex` for a cyclic subgroup is proved here from the
unconditional Morse theorem.

## The three inputs, each already isolated

* `exists_isQuasiGeodesic_pow_of_isLoxodromic` makes `fun i => g ^ i` a
  quasi-geodesic with constants uniform in the length.
* `exists_index_wordDist_le_of_isBetween_of_fourPoint` — the chord-near-chain half
  of the Morse lemma — puts every point between `1` and `g ^ N` within a
  uniform `R` of some `g ^ m`.
* A prefix of a geodesic word *is* such a point, by
  `Hyperbolic.isBetween_of_geodesic_append`.

Negative exponents are the same statement for `g⁻¹`, which is loxodromic
(`HullGeometry.isLoxodromic_inv`) and generates the same subgroup
(`Subgroup.zpowers_inv`).  Taking the larger of the two constants gives one `σ`
for all of `⟨g⟩`, which is what the predicate asks for.

## What this buys

Composed with `GGT/HullSCConeOffHeavyHyperbolic.lean`, the coned-off Cayley
graph of Hull's alphabet along the cyclic subgroups of finitely many loxodromic
elements is hyperbolic.  So clause (a) of the geometric leaf behind
`Manuscript.NonMF.TorsionFree.hullHypEmbeddedConeOff` is not an open problem in
hyperbolic geometry: it is the classical Morse lemma, already stated in
`Algebra/MorseLemma.lean` and discharged in `GGT/MorseLemmaDischarge.lean`.

Clause (b), local finiteness of the relative metric, is untouched by any of
this, and remains the expensive half of the row.

## Scope, and why the subgroup is cyclic

The live declarations use `Hyperbolic.morseLemma_univ`, so this module is
universe-polymorphic.

The subgroup here is `⟨g⟩` rather than the elementary closure `E(g)`.  That is
deliberate: `GGT/HullSCConeOffHeavyProperPower.lean` shows that `⟨g⟩` cannot be
the family in clause (b) unless `g` generates its own elementary closure, so the
family the leaf will eventually use is `E(g)`.  Quasiconvexity transports along
finite index — `⟨g⟩` has finite index in `E(g)` for a loxodromic `g` in an
acylindrical action — and that transport is not carried out here.  Clause (a) is
insensitive to the difference in any case: enlarging the coned family by a set
of bounded `A`-diameter changes neither the hypothesis nor the conclusion of
`GGT.OsinEnlargement.osinLemma55` by more than a constant.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Weakening the quasi-geodesic constants -/

/-- Both clauses of `Hyperbolic.IsQuasiGeodesic` weaken as the constants grow,
which is what lets two elements be treated at one pair of constants. -/
theorem isQuasiGeodesic_mono {G : Type} [Group G] {S : Set G}
    {K C K' C' n : ℕ} {p : ℕ → G} (hK : K ≤ K') (hC : C ≤ C')
    (h : Hyperbolic.IsQuasiGeodesic S K C n p) :
    Hyperbolic.IsQuasiGeodesic S K' C' n p := by
  intro i hi j hj hij
  obtain ⟨h1, h2⟩ := h i hi j hj hij
  refine ⟨le_trans h1 ?_, le_trans h2 ?_⟩
  · exact Nat.add_le_add (Nat.mul_le_mul hK (le_refl (j - i))) hC
  · exact Nat.mul_le_mul hK (Nat.add_le_add (le_refl _) hC)

/-! ## Prefixes of a geodesic word to a nonnegative power -/

/-- **Every prefix of an `A`-geodesic word for `h ^ N` is uniformly near
`⟨h⟩`.**

The prefix is between `1` and `h ^ N` because cutting a geodesic word produces a
between-point, and the chord-near-chain half of the Morse lemma then places it
within `R` of a vertex `h ^ m` of the power orbit.  `R` does not depend on `N`,
because the quasi-geodesic constants do not. -/
theorem exists_bound_prefix_pow_of_fourPoint
    {G : Type u} [Group G] (A : Alphabet G) {delta K C : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic A.carrier delta) {h : G}
    (hqg : ∀ n : ℕ, Hyperbolic.IsQuasiGeodesic A.carrier K C n (fun i => h ^ i)) :
    ∃ R : ℕ, ∀ (N : ℕ) (w : List G), (∀ x ∈ w, x ∈ A.carrier) →
      w.prod = h ^ N → w.length = wordDist A.carrier 1 (h ^ N) →
        ∀ i ≤ w.length, ∃ e ∈ Subgroup.zpowers h,
          wordDist A.carrier (w.take i).prod e ≤ R := by
  obtain ⟨R, hR⟩ :=
    exists_index_wordDist_le_of_isBetween_of_fourPoint K C delta
  refine ⟨R, ?_⟩
  intro N w hlet hprod hlen i _hi
  have hS := A.symmetricGenerating
  have hgw : IsGeodesicWord A.carrier w w.prod := by
    refine ⟨⟨hlet, rfl⟩, ?_⟩
    rw [hprod, hlen, wordDist_one_left]
  have hsplit : w.take i ++ w.drop i = w := List.take_append_drop i w
  have hgw' : IsGeodesicWord A.carrier (w.take i ++ w.drop i)
      (w.take i ++ w.drop i).prod := by
    rw [hsplit]
    exact hgw
  obtain ⟨hbetween, _hdist⟩ :=
    Hyperbolic.isBetween_of_geodesic_append hS (1 : G) hgw'
  rw [hsplit, one_mul, one_mul, hprod] at hbetween
  have hbet : Hyperbolic.IsBetween A.carrier ((fun m : ℕ => h ^ m) 0)
      ((w.take i).prod) ((fun m : ℕ => h ^ m) N) := by
    show Hyperbolic.IsBetween A.carrier (h ^ 0) ((w.take i).prod) (h ^ N)
    rw [pow_zero]
    exact hbetween
  obtain ⟨m, _hmN, hmle⟩ :=
    hR G inferInstance A.carrier hS hdelta N (fun m : ℕ => h ^ m) (hqg N)
      ((w.take i).prod) hbet
  have hmle' : wordDist A.carrier (h ^ m) ((w.take i).prod) ≤ R := hmle
  refine ⟨h ^ m, ?_, ?_⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]⟩
  · have hc := wordDist_comm hS (h ^ m) ((w.take i).prod)
    omega

/-! ## Quasiconvexity of the cyclic subgroup -/

/-- **The cyclic subgroup of a loxodromic element is quasiconvex in
`Γ(G,A)`**, given the Morse lemma.

The two signs are handled separately and their constants merged: `g` covers the
nonnegative powers and `g⁻¹` the negative ones, and `Subgroup.zpowers_inv` says
the two subgroups are the same. -/
theorem exists_isWordQuasiconvex_zpowers_of_fourPoint
    {G : Type u} [Group G] (A : Alphabet G) {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic A.carrier delta) {g : G}
    (hlox : IsLoxodromic g (Cayley.base A)) :
    ∃ sigma : ℕ, IsWordQuasiconvex A (Subgroup.zpowers g) sigma := by
  obtain ⟨K₁, C₁, hqg₁⟩ := exists_isQuasiGeodesic_pow_of_isLoxodromic A hlox
  have hloxinv : IsLoxodromic g⁻¹ (Cayley.base A) :=
    isLoxodromic_inv (isIsometricAction_cayley A) hlox
  obtain ⟨K₂, C₂, hqg₂⟩ := exists_isQuasiGeodesic_pow_of_isLoxodromic A hloxinv
  obtain ⟨R₁, hR₁⟩ := exists_bound_prefix_pow_of_fourPoint A hdelta hqg₁
  obtain ⟨R₂, hR₂⟩ := exists_bound_prefix_pow_of_fourPoint A hdelta hqg₂
  refine ⟨max R₁ R₂, ?_⟩
  intro b hb w hlet hprod hlen i hi
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.natAbs_eq t with hcase | hcase
  · have hbpow : b = g ^ t.natAbs := by
      have hz : g ^ ((t.natAbs : ℤ)) = b := by
        rw [← hcase]
        exact ht
      rw [← hz, zpow_natCast]
    subst hbpow
    obtain ⟨e, he, hle⟩ := hR₁ t.natAbs w hlet hprod hlen i hi
    exact ⟨e, he, le_trans hle (le_max_left _ _)⟩
  · have hbpow : b = g⁻¹ ^ t.natAbs := by
      have hz : g ^ (-(t.natAbs : ℤ)) = b := by
        rw [← hcase]
        exact ht
      rw [← hz, zpow_neg, zpow_natCast, inv_pow]
    subst hbpow
    obtain ⟨e, he, hle⟩ := hR₂ t.natAbs w hlet hprod hlen i hi
    refine ⟨e, ?_, le_trans hle (le_max_right _ _)⟩
    rwa [Subgroup.zpowers_inv] at he

/-! ## Clause (a) for a family of cyclic subgroups -/

/-- **The cone-off of Hull's alphabet along the cyclic subgroups of finitely
many loxodromic elements is hyperbolic**, given the Morse lemma.

This is clause (a) of the geometric leaf.  The family is indexed by a `Fintype`
so that the finitely many quasiconvexity constants can be merged into one; that
is the only use of finiteness, and `Bool` — the index type the leaf actually
uses — satisfies it. -/
theorem exists_hyperbolic_coneOffFamily_zpowers_of_fourPoint
    {G : Type u} [Group G] {Λ : Type} [Fintype Λ]
    (A : Alphabet G) {delta : ℝ} (hdelta : IsHyperbolicSpace delta (Cayley A))
    (g : Λ → G) (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A)) :
    ∃ delta' : ℝ, IsHyperbolicSpace delta'
      (Cayley (coneOffFamily A (fun lam => Subgroup.zpowers (g lam))).alphabet) := by
  have h4 : Hyperbolic.IsFourPointHyperbolic A.carrier ⌈delta⌉₊ :=
    GGT.isFourPointHyperbolic_of_isHyperbolicSpace_cayley A hdelta
  have hqc : ∀ lam : Λ, ∃ sigma : ℕ,
      IsWordQuasiconvex A (Subgroup.zpowers (g lam)) sigma := fun lam =>
    exists_isWordQuasiconvex_zpowers_of_fourPoint A h4 (hlox lam)
  choose sigma hsigma using hqc
  refine exists_hyperbolic_coneOffFamily_of_wordQuasiconvex A _ hdelta
    (sigma := Finset.univ.sup sigma) ?_
  intro lam b hb w hlet hprod hlen i hi
  obtain ⟨e, he, hle⟩ := hsigma lam b hb w hlet hprod hlen i hi
  exact ⟨e, he, le_trans hle (Finset.le_sup (Finset.mem_univ lam))⟩

end HullSC
end GroupApproximation
