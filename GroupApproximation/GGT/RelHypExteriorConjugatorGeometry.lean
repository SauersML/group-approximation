import GroupApproximation.GGT.RelHypFournierFacioGeometricBoundary
import GroupApproximation.GGT.ElementaryMorseAlphabet

/-!
# Geometry of the exterior conjugator in the non-commensurable-pair boundary

`RelHypFournierFacioGeometricBoundary` constructs two infinite-order elements
`g,t` with no equal nonzero powers and proves that any witness of
`OsinCommensurable g t` must use a conjugator outside Osin's elementary closure
of `g`.  This module closes every further unconditional step available from the
finite-Cayley geometry.

For a loxodromic element the set-valued Osin elementary closure used by
Fournier--Facio agrees with the subgroup-valued elementary closure used by the
acylindrical-action machinery.  Consequently a surviving conjugator is outside
the latter subgroup as well.  It therefore moves the axis of `g` to an
independent loxodromic direction.  The commensurability equation simultaneously
places `t` in the elementary closure of that conjugate direction.

This is the exact exterior-conjugator configuration:

* `g` and `t` are directly power-separated;
* `g` and `c⁻¹gc` are independent;
* `t` and `c⁻¹gc` share a nonzero power.

There is no contradiction: the free-group example `t = c⁻¹gc` realizes all
three clauses.  Thus the remaining theorem is genuinely the uniform choice of
`t` outside the power classes of **every** conjugate of `g`, not another
centralizer or elementary-closure calculation.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## 1.  The exact all-conjugators predicate -/

/-- Direct nonzero-power separation from every conjugate of `g`.  This is the
conjugator-exposed form of `¬ OsinCommensurable g t`. -/
def ConjugacyUniformZpowSeparated {H : Type*} [Group H] (g t : H) : Prop :=
  ∀ (c : H) (k l : ℤ), k ≠ 0 → l ≠ 0 → c⁻¹ * g ^ k * c ≠ t ^ l

/-- Osin non-commensurability is exactly uniform direct-power separation over
all ambient conjugators. -/
theorem conjugacyUniformZpowSeparated_iff_not_osinCommensurable
    {H : Type*} [Group H] {g t : H} :
    ConjugacyUniformZpowSeparated g t ↔ ¬ OsinCommensurable g t := by
  constructor
  · intro hsep hcomm
    obtain ⟨k, l, c, hk, hl, heq⟩ := hcomm
    exact hsep c k l hk hl heq
  · intro hnc c k l hk hl heq
    exact hnc ⟨k, l, c, hk, hl, heq⟩

/-- Thus the still-open pair statement is precisely the existence of an
infinite-order pair separated from every conjugate, with no hidden
elementary-closure or torsion clause. -/
theorem hyperbolicNonCommensurablePairStatement_iff_conjugacyUniform :
    HyperbolicNonCommensurablePairStatement ↔
      ∀ (H : Type) (_ : Group H),
        IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
          ∃ g t : H,
            (∀ n : ℕ, 0 < n → g ^ n ≠ 1) ∧
            (∀ n : ℕ, 0 < n → t ^ n ≠ 1) ∧
            ConjugacyUniformZpowSeparated g t := by
  constructor
  · intro h H instH hne htf
    obtain ⟨g, t, hg, ht, hnc⟩ := h H instH hne htf
    exact ⟨g, t, hg, ht,
      conjugacyUniformZpowSeparated_iff_not_osinCommensurable.mpr hnc⟩
  · intro h H instH hne htf
    obtain ⟨g, t, hg, ht, hsep⟩ := h H instH hne htf
    exact ⟨g, t, hg, ht,
      conjugacyUniformZpowSeparated_iff_not_osinCommensurable.mp hsep⟩

/-! ## 2.  The two elementary-closure definitions agree on loxodromics -/

/-- For a loxodromic `g`, subgroup-valued elementary-closure membership implies
membership in Osin's positive-natural-exponent `±` closure.

Apply the positive-exponent normalisation to `c⁻¹ ∈ E(g)`.  Its conjugation
orientation is exactly the one in `osinElementaryClosure`. -/
theorem mem_osinElementaryClosure_of_mem_elementaryClosure_of_isLoxodromic
    {H X : Type*} [Group H] [PseudoMetricSpace X] [MulAction H X]
    (hiso : IsIsometricAction H X) {x : X} {g c : H}
    (hg : IsLoxodromic g x) (hc : c ∈ Elementary.elementaryClosure g) :
    c ∈ osinElementaryClosure g := by
  have hcinv : c⁻¹ ∈ Elementary.elementaryClosure g :=
    (Elementary.elementaryClosure g).inv_mem hc
  obtain ⟨n, hn, hpos | hneg⟩ :=
    Elementary.exists_conj_positive_zpow_eq_or_of_mem_elementaryClosure
      hiso hg hcinv
  · refine ⟨n, hn, Or.inl ?_⟩
    simpa [zpow_natCast] using hpos
  · refine ⟨n, hn, Or.inr ?_⟩
    simpa [zpow_natCast, zpow_neg] using hneg

/-- Hence the two closure predicates coincide on loxodromic elements. -/
theorem mem_osinElementaryClosure_iff_mem_elementaryClosure_of_isLoxodromic
    {H X : Type*} [Group H] [PseudoMetricSpace X] [MulAction H X]
    (hiso : IsIsometricAction H X) {x : X} {g c : H}
    (hg : IsLoxodromic g x) :
    c ∈ osinElementaryClosure g ↔ c ∈ Elementary.elementaryClosure g := by
  constructor
  · exact mem_elementaryClosure_of_mem_osinElementaryClosure
  · exact mem_osinElementaryClosure_of_mem_elementaryClosure_of_isLoxodromic
      hiso hg

/-! ## 3.  The exterior witness creates an independent conjugate axis -/

/-- A commensurability witness for a directly power-separated pair has its
conjugator outside the subgroup-valued elementary closure as well. -/
theorem not_mem_elementaryClosure_of_commensurability_witness
    {H X : Type*} [Group H] [PseudoMetricSpace X] [MulAction H X]
    (hiso : IsIsometricAction H X) {x : X} {g t c : H} {k l : ℤ}
    (hg : IsLoxodromic g x) (hk : k ≠ 0) (hl : l ≠ 0)
    (hconj : c⁻¹ * g ^ k * c = t ^ l)
    (hsep : ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m) :
    c ∉ Elementary.elementaryClosure g := by
  intro hc
  exact not_mem_osinElementaryClosure_of_commensurability_witness
    hk hl hconj hsep
    (mem_osinElementaryClosure_of_mem_elementaryClosure_of_isLoxodromic
      hiso hg hc)

/-- The complete geometry forced by a surviving commensurability witness.

The exterior conjugator makes `g` independent from its conjugate, while the
commensurability equation says `t` lies in the elementary closure of that
conjugate. -/
theorem commensurability_witness_exterior_geometry
    {H : Type*} [Group H] (A : Alphabet H) (hAfin : A.carrier.Finite)
    {delta : ℝ} (hdelta : IsHyperbolicSpace delta (Cayley A))
    {g t c : H} {k l : ℤ} (hgfin : ¬ IsOfFinOrder g)
    (hk : k ≠ 0) (hl : l ≠ 0) (hconj : c⁻¹ * g ^ k * c = t ^ l)
    (hsep : ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m) :
    c ∉ Elementary.elementaryClosure g ∧
      Independent g (c⁻¹ * g * c) (Cayley.base A) ∧
        t ∈ Elementary.elementaryClosure (c⁻¹ * g * c) := by
  have hglox : IsLoxodromic g (Cayley.base A) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      A hAfin hdelta hgfin
  have hcout : c ∉ Elementary.elementaryClosure g :=
    not_mem_elementaryClosure_of_commensurability_witness
      (isIsometricAction_cayley A) hglox hk hl hconj hsep
  have hcinv : c⁻¹ ∉ Elementary.elementaryClosure g := by
    intro hc
    apply hcout
    simpa only [inv_inv] using (Elementary.elementaryClosure g).inv_mem hc
  have hind : Independent g (c⁻¹ * g * c) (Cayley.base A) := by
    have h := Elementary.independent_conj_of_notMem_elementaryClosure
      (isIsometricAction_cayley A)
      (ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic
        A hdelta (isAcylindrical_cayley_of_finite A hAfin))
      hglox hcinv
    simpa only [inv_inv] using h
  have hpow : (c⁻¹ * g * c) ^ k = t ^ l := by
    calc
      (c⁻¹ * g * c) ^ k = c⁻¹ * g ^ k * c := by
        simpa only [inv_inv] using (Elementary.conj_zpow_eq c⁻¹ g k).symm
      _ = t ^ l := hconj
  have htmem : t ∈ Elementary.elementaryClosure (c⁻¹ * g * c) :=
    Elementary.mem_elementaryClosure_of_common_zpow hk hpow
  exact ⟨hcout, hind, htmem⟩

/-! ## 4.  The maximal unconditional pair package -/

/-- Every torsion-free non-elementary hyperbolic group contains a directly
power-separated infinite-order pair for which every hypothetical
commensurability witness has the exterior geometry above.

This theorem packages the strongest presently provable conclusion without a
uniform commensurability-class avoidance theorem. -/
theorem exists_pair_with_exterior_commensurability_geometry
    {H : Type} [Group H] (hne : IsNonElementaryHyperbolic H)
    (htf : IsPowerTorsionFree H) :
    ∃ (A : Alphabet H) (delta : ℝ) (g t : H),
      A.carrier.Finite ∧ IsHyperbolicSpace delta (Cayley A) ∧
      (∀ n : ℕ, 0 < n → g ^ n ≠ 1) ∧
      (∀ n : ℕ, 0 < n → t ^ n ≠ 1) ∧
      (∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m) ∧
      ∀ (c : H) (k l : ℤ), k ≠ 0 → l ≠ 0 →
        c⁻¹ * g ^ k * c = t ^ l →
          c ∉ Elementary.elementaryClosure g ∧
          Independent g (c⁻¹ * g * c) (Cayley.base A) ∧
          t ∈ Elementary.elementaryClosure (c⁻¹ * g * c) := by
  obtain ⟨T, hT, delta, hdelta⟩ := hne.1
  let A : Alphabet H := ⟨(T : Set H), hT⟩
  have hAfin : A.carrier.Finite := T.finite_toSet
  have hAδ : IsHyperbolicSpace (delta : ℝ) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hdelta
  obtain ⟨g, t, hgord, htord, hsep⟩ :=
    exists_infiniteOrder_pair_no_common_zpow hne htf
  have hg1 : g ≠ 1 := by
    intro hg
    exact hgord 1 one_pos (by simp [hg])
  have hgfin : ¬ IsOfFinOrder g := htf.not_isOfFinOrder hg1
  refine ⟨A, (delta : ℝ), g, t, hAfin, hAδ, hgord, htord, hsep, ?_⟩
  intro c k l hk hl hconj
  exact commensurability_witness_exterior_geometry
    A hAfin hAδ hgfin hk hl hconj hsep

end RelHyp
end GGT
end GroupApproximation
