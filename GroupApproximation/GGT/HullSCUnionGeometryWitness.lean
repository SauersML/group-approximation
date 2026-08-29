import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor
import GroupApproximation.GGT.ElementaryCentralizerAxis
import GroupApproximation.GGT.ElementaryMorseOrbit

/-!
# The two witnesses, and what is left of the second

`GGT/HullSCUnionGeometryHyperbolicFactor.lean` reduced the third field of a Hull
generating set on a hyperbolic group to two witnesses: an element `g` of
infinite order, and an element `t` outside its elementary closure.  This module
disposes of the first and sharpens the second.

## The first witness is free

`HullSC.FreeProductUnionGeometryStatement` already carries `IsPowerTorsionFree H`
and `Infinite H`.  An infinite group is nontrivial, and in a torsion-free group
every nontrivial element has infinite order, so
`exists_not_isOfFinOrder_of_infinite` supplies `g` outright --- Gromov's theorem
that an infinite hyperbolic group is not torsion is never needed here.

## The second witness, without the elementary closure

`E(g)` is a conjugation condition, and awkward to check.  Under an acylindrical
action on a hyperbolic space and over a torsion-free ambient group it collapses
to a *commensurability* condition: Osin's centralizer theorem, in the repository
as `GGT.Elementary.exists_common_zpow_of_mem_elementaryClosure_of_axis`, says
that every nontrivial `c ∈ E(g)` satisfies `gⁱ = cᵐ` for some nonzero `i, m`.

Its four geometric inputs are all available at a finite alphabet, and the last
of them --- the Morse residual `CentralizerOrbitNearAxis` --- is de-circularised
here exactly as Bowditch's dichotomy and the common-power criterion were:
`centralizerOrbitNearAxis_cayley_of_alphabet` needs the metric realisation and
hyperbolicity of the vertex metric, and nothing else.  So
`notMem_elementaryClosure_of_no_common_zpow` reduces the second witness to

> some `t ≠ 1` shares no nonzero power with `g`,

a statement with no conjugation, no elementary closure and no geometry in it.

## What is still owed

Exactly that statement.  It is where non-elementarity is really being used: if
*every* `t ≠ 1` shared a nonzero power with `g` then every element of `H` would
commensurate `⟨g⟩`, and for a hyperbolic `H` that forces `H` virtually cyclic,
contradicting `GGT.RelHyp.not_isElementaryGroup_of_infinite_of_kazhdan'`.  The
missing step is the virtual cyclicity: the orientation-preserving elements form a
subgroup of index at most two, and it is finite modulo `⟨g⟩` by acylindricity ---
which needs the quasi-axis of `g` and a displacement normalisation along it.

Note the hypothesis alone does *not* suffice: a central extension of an infinite
finitely generated torsion group by `ℤ` is finitely generated, torsion-free, and
has every element with a power in the central `ℤ`, yet is not virtually cyclic.
Hyperbolicity of `H` is doing real work in that step, so it cannot be replaced by
a purely algebraic argument.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## 1.  The Morse residual at any hyperbolic alphabet -/

/-- **`CentralizerOrbitNearAxis` at `Γ(G,A)`**, from hyperbolicity of the vertex
metric alone.  The same proof as `GGT.ElementaryMorse.centralizerOrbitNearAxis_cayley`,
with the `HullGeneratingSet` replaced by `hasGeodesicModel_of_alphabet`; note the
geodesic-space statement needs no acylindricity at all. -/
theorem centralizerOrbitNearAxis_cayley_of_alphabet {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A)) :
    GGT.Elementary.CentralizerOrbitNearAxis G (Cayley.base A) := by
  obtain ⟨M⟩ := hasGeodesicModel_of_alphabet A hδ
  exact GGT.Elementary.centralizerOrbitNearAxis_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (GGT.ElementaryMorse.centralizerOrbitNearAxis_of_geodesic M.hyperbolic
      M.delta_nonneg M.geodesic M.isometric _)

/-! ## 2.  The elementary closure is a commensurability condition -/

/-- **Osin's centralizer theorem at a finite alphabet.**  Over a torsion-free
group, every nontrivial element of `E(g)` shares a nonzero power with `g`.  All
four geometric inputs are theorems here: the action is isometric and --- the
alphabet being finite --- acylindrical, and the Morse residual and Bowditch's
dichotomy are `centralizerOrbitNearAxis_cayley_of_alphabet` and
`escapingIsLoxodromic_cayley_of_acylindrical`. -/
theorem exists_common_zpow_of_mem_elementaryClosure_cayley {G : Type u} [Group G]
    (A : Alphabet G) (hfin : A.carrier.Finite) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) (htf : IsPowerTorsionFree G)
    {g c : G} (hg : ¬ IsOfFinOrder g)
    (hc : c ∈ GGT.Elementary.elementaryClosure g) (hc1 : c ≠ 1) :
    ∃ i m : ℤ, i ≠ 0 ∧ m ≠ 0 ∧ g ^ i = c ^ m :=
  GGT.Elementary.exists_common_zpow_of_mem_elementaryClosure_of_axis
    (isIsometricAction_cayley A) (GGT.isAcylindrical_cayley_of_finite A hfin)
    (centralizerOrbitNearAxis_cayley_of_alphabet A hδ)
    (escapingIsLoxodromic_cayley_of_acylindrical A hδ
      (GGT.isAcylindrical_cayley_of_finite A hfin))
    htf (isLoxodromic_cayley_of_not_isOfFinOrder A hfin hδ hg) hc hc1

/-- **Sharing no power with `g` puts an element outside `E(g)`.**  The
contrapositive of the previous theorem, and the form the Hull generating set
consumes. -/
theorem notMem_elementaryClosure_of_no_common_zpow {G : Type u} [Group G]
    (A : Alphabet G) (hfin : A.carrier.Finite) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) (htf : IsPowerTorsionFree G)
    {g t : G} (hg : ¬ IsOfFinOrder g)
    (hnc : ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m) (ht1 : t ≠ 1) :
    t ∉ GGT.Elementary.elementaryClosure g := by
  intro hmem
  obtain ⟨i, m, hi, hm, he⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_cayley A hfin hδ htf hg hmem ht1
  exact hnc i m hi hm he

/-! ## 3.  The first witness is free -/

/-- **An infinite torsion-free group has an element of infinite order.**  It is
nontrivial, and in a torsion-free group every nontrivial element has infinite
order. -/
theorem exists_not_isOfFinOrder_of_infinite {H : Type u} [Group H]
    (hinf : Infinite H) (htf : IsPowerTorsionFree H) :
    ∃ g : H, ¬ IsOfFinOrder g := by
  haveI := hinf
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset ({1} : Finset H)
  refine ⟨g, htf.not_isOfFinOrder ?_⟩
  simpa using hg

/-! ## 4.  The residue of the free product input -/

/-- **`HullSC.FreeProductUnionGeometryStatement` from acylindricity of the union
alphabet and one commensurability witness in `H`.**

Both hypotheses are what the lane still owes, and nothing else is:

* `hacyl` --- the translation action of `E ∗ H` on `Γ(E ∗ H, A ⊔ B)` is
  acylindrical; the tree-of-spaces crossing estimate.
* `hwit` --- an infinite torsion-free hyperbolic group with property `(T)` has,
  for each element `g` of infinite order, some `t ≠ 1` sharing no nonzero power
  with `g`.

The second is the whole of non-elementarity of `H`, with the geometry stripped
out: no Cayley graph, no elementary closure, no conjugation. -/
theorem freeProductUnionGeometryStatement_of_noCommonZpow
    (hacyl : ∀ (E H : Type) [Group E] [Group H] (A : HullGeneratingSet E)
      (B : HullGeneratingSet H),
        IsAcylindrical (Monoid.Coprod E H)
          (Cayley (HullSC.unionAlphabet A.alphabet B.alphabet)))
    (hwit : ∀ (H : Type) [Group H], Infinite H → IsPowerTorsionFree H →
      GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
        HasKazhdanPropertyT.{0, 0} H →
          ∀ g : H, ¬ IsOfFinOrder g →
            ∃ t : H, t ≠ 1 ∧ ∀ i m : ℤ, i ≠ 0 → m ≠ 0 → g ^ i ≠ t ^ m) :
    HullSC.FreeProductUnionGeometryStatement := by
  intro E H instE instH _hEfp _hHfp _hEtf hHtf hEah hHinf hHhyp hHT
  letI := instE
  letI := instH
  haveI := hEah
  obtain ⟨A⟩ := exists_hullGeneratingSet E
  obtain ⟨g, hg⟩ := exists_not_isOfFinOrder_of_infinite hHinf hHtf
  obtain ⟨t, ht1, hnc⟩ := hwit H hHinf hHtf hHhyp hHT g hg
  obtain ⟨T, hTsym, δ, hδ⟩ := hHhyp
  have hB : HullGeneratingSet H :=
    hullGeneratingSetOfWitness hTsym hδ hg
      (notMem_elementaryClosure_of_no_common_zpow
        (⟨(T : Set H), hTsym⟩ : Alphabet H) T.finite_toSet
        (GGT.isHyperbolicSpace_cayley_of_fourPoint _ hδ) hHtf hg hnc ht1)
  obtain ⟨δ', hδ'⟩ := exists_isHyperbolicSpace_cayley_unionAlphabet A hB
  exact ⟨A, hB, δ', hδ', hacyl E H A hB⟩

end HullSCUnionGeometry
end GroupApproximation
