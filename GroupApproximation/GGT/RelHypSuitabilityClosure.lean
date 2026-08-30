import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor
import GroupApproximation.GGT.RelHypSuitabilityResidue

/-!
# The elementary-closure half of hyperbolic suitability

This module separates the two ingredients of
`RelHyp.HyperbolicElementaryClosureStatement`.

The geometric input is Osin's Theorem 6.8, in the already established form
`Elementary.ElementaryClosureVirtuallyCyclic`: every infinite subgroup of the
elementary closure of a loxodromic element contains a nonzero power of that
element.  Everything after that input is algebra.  In particular, the desired
trivial-intersection conclusion does **not** require choosing a primitive root
or proving the stronger classification "torsion-free virtually cyclic implies
cyclic".  A nontrivial element in two elementary closures shares a nonzero
power with both loxodromics; aligning the two equalities makes the loxodromics
commensurable.

The only use of torsion-freeness is to turn the two nontrivial witnesses into
infinite-order elements.  Properness of a finite Cayley graph and Bowditch's
dichotomy then make them loxodromic; that part is already proved in
`HullSCUnionGeometryHyperbolicFactor`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT.Elementary

/-! ## 1.  The two elementary-closure vocabularies -/

/-- Membership in Osin's positive-power `±` definition implies membership in
the subgroup-valued commensurator definition.

The former conjugates by `f⁻¹`, while the latter conjugates by its member on
the left.  We first put `f⁻¹` in the subgroup and then use inverse closure. -/
theorem mem_elementaryClosure_of_mem_osinElementaryClosure
    {G : Type*} [Group G] {g f : G}
    (hf : f ∈ osinElementaryClosure g) :
    f ∈ elementaryClosure g := by
  obtain ⟨n, hn, hsame | hinv⟩ := hf
  · have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hfinv : f⁻¹ ∈ elementaryClosure g := by
      refine mem_elementaryClosure.mpr ⟨(n : ℤ), (n : ℤ), hn0, hn0, ?_⟩
      simpa [zpow_natCast] using hsame
    simpa using (elementaryClosure g).inv_mem hfinv
  · have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hfinv : f⁻¹ ∈ elementaryClosure g := by
      refine mem_elementaryClosure.mpr
        ⟨(n : ℤ), -(n : ℤ), hn0, neg_ne_zero.mpr hn0, ?_⟩
      simpa [zpow_natCast, zpow_neg] using hinv
    simpa using (elementaryClosure g).inv_mem hfinv

/-! ## 2.  The torsion-free algebra after Osin 6.8 -/

/-- A nontrivial common member of two elementary closures forces the two
loxodromics to be commensurable.

This is the exact algebraic upgrade needed by suitability.  Torsion-freeness
enters only through
`exists_common_zpow_of_mem_elementaryClosure_of_torsionFree`; the conclusion is
obtained by aligning the two common-power equalities. -/
theorem osinCommensurable_of_mem_two_elementaryClosures_of_torsionFree
    {G X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X] {x : X}
    (hvc : ElementaryClosureVirtuallyCyclic G x)
    (htf : IsPowerTorsionFree G) {g k f : G}
    (hg : IsLoxodromic g x) (hk : IsLoxodromic k x)
    (hf : f ≠ 1) (hfg : f ∈ elementaryClosure g)
    (hfk : f ∈ elementaryClosure k) :
    OsinCommensurable g k := by
  obtain ⟨i, m, hi, hm, hgm⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_of_torsionFree
      hvc htf hg hfg hf
  obtain ⟨j, n, hj, hn, hkn⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_of_torsionFree
      hvc htf hk hfk hf
  refine ⟨i * n, j * m, 1, mul_ne_zero hi hn, mul_ne_zero hj hm, ?_⟩
  have hcommon : g ^ (i * n) = k ^ (j * m) := by
    calc
      g ^ (i * n) = (g ^ i) ^ n := by rw [zpow_mul]
      _ = (f ^ m) ^ n := by rw [hgm]
      _ = f ^ (m * n) := by rw [← zpow_mul]
      _ = f ^ (n * m) := by rw [mul_comm m n]
      _ = (f ^ n) ^ m := by rw [zpow_mul]
      _ = (k ^ j) ^ m := by rw [← hkn]
      _ = k ^ (j * m) := by rw [← zpow_mul]
  simpa using hcommon

/-- Consequently two non-commensurable loxodromics have trivially meeting
Osin elementary closures. -/
theorem eq_one_of_mem_two_osinElementaryClosures_of_torsionFree
    {G X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X] {x : X}
    (hvc : ElementaryClosureVirtuallyCyclic G x)
    (htf : IsPowerTorsionFree G) {g k f : G}
    (hg : IsLoxodromic g x) (hk : IsLoxodromic k x)
    (hnc : ¬ OsinCommensurable g k)
    (hfg : f ∈ osinElementaryClosure g)
    (hfk : f ∈ osinElementaryClosure k) : f = 1 := by
  by_contra hf
  exact hnc (osinCommensurable_of_mem_two_elementaryClosures_of_torsionFree
    hvc htf hg hk hf
    (mem_elementaryClosure_of_mem_osinElementaryClosure hfg)
    (mem_elementaryClosure_of_mem_osinElementaryClosure hfk))

/-! ## 3.  Exact remaining geometric input and final assembly -/

/-- Osin's Theorem 6.8 at a finite hyperbolic Cayley alphabet.

The alphabet's finiteness already supplies acylindricity of the translation
action, so this proposition isolates exactly the still-unproved geometry and
does not repeat that theorem as a premise. -/
def OsinTheorem68FiniteCayleyStatement : Prop :=
  ∀ (G : Type) (_ : Group G) (A : Alphabet G), A.carrier.Finite →
    ∀ δ : ℝ, IsHyperbolicSpace δ (Cayley A) →
      ElementaryClosureVirtuallyCyclic G (Cayley.base A)

/-- Osin's Theorem 6.8 closes half (b) of hyperbolic suitability.

After unpacking the finite hyperbolic alphabet, torsion-freeness makes each
nontrivial witness infinite-order, the finite-Cayley theorem makes it
loxodromic, and the algebraic theorem above gives the required trivial
intersection. -/
theorem hyperbolicElementaryClosureStatement_of_osinTheorem68
    (h68 : OsinTheorem68FiniteCayleyStatement) :
    HyperbolicElementaryClosureStatement := by
  intro G _instG hG htf g k hgord hkord hnc f hfg hfk
  obtain ⟨T, hT, δ, hδ⟩ := hG.1
  let A : Alphabet G := ⟨(T : Set G), hT⟩
  have hAfin : A.carrier.Finite := T.finite_toSet
  have hAδ : IsHyperbolicSpace (δ : ℝ) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hδ
  have hg1 : g ≠ 1 := by
    intro hg1
    exact hgord 1 zero_lt_one (by simp [hg1])
  have hk1 : k ≠ 1 := by
    intro hk1
    exact hkord 1 zero_lt_one (by simp [hk1])
  have hglox : IsLoxodromic g (Cayley.base A) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      A hAfin hAδ (htf.not_isOfFinOrder hg1)
  have hklox : IsLoxodromic k (Cayley.base A) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      A hAfin hAδ (htf.not_isOfFinOrder hk1)
  exact eq_one_of_mem_two_osinElementaryClosures_of_torsionFree
    (h68 G _instG A hAfin (δ : ℝ) hAδ) htf hglox hklox hnc hfg hfk

end RelHyp
end GGT
end GroupApproximation
