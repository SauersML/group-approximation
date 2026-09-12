import GroupApproximation.GGT.ElementaryCentralizerAxis
import GroupApproximation.GGT.HyperbolicAdditiveTransfer

/-!
# Transporting the Osin residuals from a geodesic model to `Γ(G,A)`

The residuals of `GGT.ElementaryCentralizerAxis` --- `CentralizerOrbitNearAxis`,
`EscapingIsLoxodromic`, `HasLoxodromicOfUnbounded`, `IndependentOfNoCommonZpow`
--- are Morse-type statements, and Morse stability is a statement about
quasi-geodesics compared with genuine geodesics.  `Cayley A` is the vertex set of
`Γ(G,A)` with the word metric, so all of its distances are natural numbers and it
is **not** a geodesic space: a segment of length at least one would have to
realise the distance `1/2` between two of its points.  So the residuals will be
proved in a geodesic model `Y` of `Γ(G,A)` and consumed at `Γ(G,A)` itself.

This module is the layer between.  All four transport backwards along any
equivariant map `f : X → Y` of bounded additive distortion --- the vertex
inclusion of `Γ(G,A)` into the metric realisation of the graph is one, with
distortion `0` --- and the transport is the four one-line consequences of
`GGT.HyperbolicAdditiveTransfer`'s `isLoxodromic_map`, `isLoxodromic_of_map` and
`independent_of_map`, plus `isEscaping_map` proved here.

The direction matters and is the same for all four: each residual is a statement
one *assumes* at `f x` and *concludes* at `x`.  Loxodromy is needed in the
pushing-forward direction inside three of the proofs (to feed the `Y`-side
hypothesis) and in the pulling-back direction to return the conclusion, and both
directions are available at the same cost because additive distortion is a
`(1, C)`-quasi-isometric embedding.

## No dependency on a particular model

`GGT.CayleyGeodesicModel` and `Manuscript.NonMF.HullFillAxisDichotomy` are not
imported.  The Cayley-level statement below takes the comparison map and its two
properties as explicit hypotheses, so any model that produces an equivariant map
of bounded additive distortion out of `Cayley A.alphabet` feeds it, and nothing
in the root import list depends on which model that is.

Acylindricity and non-elementarity of `Γ(G,A)` are not transported: they are
fields of `HullGeneratingSet` already.  Acylindricity would transport anyway, by
`isAcylindrical_of_additiveDistortion`, which needs no density hypothesis.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v w

section Transfer

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}
  [PseudoMetricSpace X] [PseudoMetricSpace Y] [MulAction G X] [MulAction G Y]

/-- **Escape pushes forward.**  The displacement sequence changes by at most the
distortion, and a bounded perturbation does not affect divergence. -/
theorem isEscaping_map {C : ℝ} {f : X → Y} (hf : HasAdditiveDistortion C f)
    (hequiv : IsEquivariant G f) {g : G} {x : X} (hg : IsEscaping g x) :
    IsEscaping g (f x) := by
  rw [IsEscaping, Filter.tendsto_atTop]
  intro A
  have hev := hg.eventually_ge_atTop (A + C)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 := hf x ((g ^ n) • x)
  rw [hequiv (g ^ n) x] at h2
  have h2a := (abs_le.mp h2).1
  linarith

/-- **Bowditch's dichotomy pulls back.**  Escape pushes forward and loxodromy
pulls back, so the dichotomy at `f x` gives the dichotomy at `x`. -/
theorem escapingIsLoxodromic_of_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {x : X}
    (h : EscapingIsLoxodromic G (f x)) : EscapingIsLoxodromic G x := by
  intro c hc
  exact isLoxodromic_of_map hC hf hequiv (h c (isEscaping_map hf hequiv hc))

/-- **The common-power criterion pulls back.**  Having no common nonzero power
is a statement about the group alone, so it crosses unchanged; loxodromy pushes
forward to feed the hypothesis, and independence pulls back. -/
theorem independentOfNoCommonZpow_of_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {x : X}
    (h : IndependentOfNoCommonZpow G (f x)) : IndependentOfNoCommonZpow G x := by
  intro a b ha hb hnp
  exact independent_of_map hf hequiv
    (h a b (isLoxodromic_map hC hf hequiv ha) (isLoxodromic_map hC hf hequiv hb)
      hnp)

/-- **The classification pulls back.**  An orbit bounded at `f x` is bounded at
`x` up to the distortion, so an unbounded orbit at `x` is unbounded at `f x`;
the loxodromic element it produces then pulls back. -/
theorem hasLoxodromicOfUnbounded_of_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {x : X}
    (h : HasLoxodromicOfUnbounded G (f x)) : HasLoxodromicOfUnbounded G x := by
  intro K hunb
  have hunbY : ¬ ∃ B : ℝ, ∀ c ∈ K, dist (f x) (c • f x) ≤ B := by
    rintro ⟨B, hB⟩
    refine hunb ⟨B + C, fun y hy => ?_⟩
    have h2 := hf x (y • x)
    rw [hequiv y x] at h2
    have h2a := (abs_le.mp h2).1
    have h3 := hB y hy
    linarith
  obtain ⟨c, hcK, hc⟩ := h K hunbY
  exact ⟨c, hcK, isLoxodromic_of_map hC hf hequiv hc⟩

/-- **The Morse residual pulls back.**  The comparison map moves the distance
between the two orbit points by at most the distortion, so the bound grows by
`C` and the partner exponent is unchanged. -/
theorem centralizerOrbitNearAxis_of_map {C : ℝ} (hC : 0 ≤ C) {f : X → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f) {x : X}
    (h : CentralizerOrbitNearAxis G (f x)) : CentralizerOrbitNearAxis G x := by
  intro q hq
  obtain ⟨K, hK0, hK⟩ := h q (isLoxodromic_map hC hf hequiv hq)
  refine ⟨K + C, by linarith, ?_⟩
  intro c hcq k
  obtain ⟨j, hj⟩ := hK c hcq k
  refine ⟨j, ?_⟩
  have h2 := hf ((c ^ k) • x) ((q ^ j) • x)
  rw [hequiv (c ^ k) x, hequiv (q ^ j) x] at h2
  have h2a := (abs_le.mp h2).1
  linarith

/-- **Osin's Lemma 7.1 at the source, from the residuals at the model.**  All
four Morse-type residuals are assumed at `f x`, where the geodesic argument can
be run; the conclusion is at `x`.  Isometry and acylindricity are assumed at `x`,
where `Γ(G,A)` already carries them. -/
theorem actsNonElementarily_of_isSNormal_of_map_of_torsionFree {C : ℝ}
    (hC : 0 ≤ C) {f : X → Y} (hf : HasAdditiveDistortion C f)
    (hequiv : IsEquivariant G f) (hisoX : IsIsometricAction G X)
    (hacyX : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G (f x))
    (hbow : EscapingIsLoxodromic G (f x))
    (hlox : HasLoxodromicOfUnbounded G (f x))
    (hindep : IndependentOfNoCommonZpow G (f x))
    (htf : IsPowerTorsionFree G)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x)
    {N : Subgroup G} (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N x :=
  actsNonElementarily_of_isSNormal_of_torsionFree hisoX hacyX
    (centralizerOrbitNearAxis_of_map hC hf hequiv hnear)
    (escapingIsLoxodromic_of_map hC hf hequiv hbow)
    (hasLoxodromicOfUnbounded_of_map hC hf hequiv hlox)
    (independentOfNoCommonZpow_of_map hC hf hequiv hindep) htf hG hN

end Transfer

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The manuscript's statement, with the residuals discharged in a geodesic
model.**

This is `HullInputsCorrected.osinNonElementary` over a torsion-free ambient
group --- the only case `lem:saturation` uses --- with every Morse-type
hypothesis moved to a space `Y` where geodesics exist.  The model enters only as
an equivariant map of bounded additive distortion out of the vertex set, so any
construction supplying one feeds this theorem, and nothing here depends on which.

The vertex inclusion of `Γ(G,A)` into the metric realisation of the graph has
distortion `0`, so `C = 0` is the intended instance and the constants below do
not grow at all. -/
theorem osinNonElementary_of_torsionFree_of_model {G : Type u} [Group G]
    (A : HullGeneratingSet G) {Y : Type w} [PseudoMetricSpace Y]
    [MulAction G Y] {C : ℝ} (hC : 0 ≤ C) {f : Cayley A.alphabet → Y}
    (hf : HasAdditiveDistortion C f) (hequiv : IsEquivariant G f)
    (hnear : CentralizerOrbitNearAxis G (f (Cayley.base A.alphabet)))
    (hbow : EscapingIsLoxodromic G (f (Cayley.base A.alphabet)))
    (hlox : HasLoxodromicOfUnbounded G (f (Cayley.base A.alphabet)))
    (hindep : IndependentOfNoCommonZpow G (f (Cayley.base A.alphabet)))
    (htf : IsPowerTorsionFree G) (N : Subgroup G)
    (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  actsNonElementarily_of_isSNormal_of_map_of_torsionFree hC hf hequiv
    A.isometric A.acylindrical hnear hbow hlox hindep htf A.nonElementary hN

end Cayley

end Elementary
end GGT
end GroupApproximation
