import GroupApproximation.GGT.GuessingGeodesicsCriterion
import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

/-!
# Clause (a) of the cone-off leaf, reduced to quasiconvexity

`GGT.RelGenSet.IsHyperbolicallyEmbedded` has two clauses: (a) the coned-off
Cayley graph is hyperbolic, (b) every relative ball is finite.  For the cone-off
of Hull's alphabet along a family of subgroups, this module discharges (a) from
one geometric input, and that input is quasiconvexity of the coned subgroups.

## Why (a) is the cheap clause

`GGT.OsinEnlargement.osinLemma55` --- proved, not assumed, in
`GGT/GuessingGeodesicsCriterion.lean` by way of Bowditch's guessing-geodesics
criterion --- says that enlarging an alphabet preserves hyperbolicity as soon as
the old geodesics joining the endpoints of the new letters stay boundedly far
from the basepoint **in the new metric**.  The coned-off alphabet is an
enlargement of Hull's, and its new letters are exactly the elements of the
subgroups, so the hypothesis reads: an `A`-geodesic word for an element of
`K λ` has all its prefixes at bounded distance from `1` in the coned metric.

That is what quasiconvexity buys, and cheaply.  Each element of `K λ` is a
single letter of the coned alphabet, hence at coned distance one from `1`; so a
prefix within `σ` of `K λ` in the `A`-metric is within `σ + 1` of `1` in the
coned metric, because the coned metric is the smaller of the two.  The constant
is `σ + 1` and nothing else enters.

The point is that the elements of `K λ` are *already letters*: the cone is doing
the work, and the estimate does not have to survive a change of basepoint or a
choice of representatives.  This is where the combinatorial cone-off is better
behaved than Dahmani--Guirardel--Osin's, whose relative generating set is
constructed one element per edge of a projection complex (arXiv:1111.7048,
p.60) precisely so that its letters have bounded displacement.  In a Cayley
graph every letter has displacement one for free.

## What is left

`IsWordQuasiconvex` is stated here so that the residue is visible and can be
model-tested.  It is not proved here, and the route to it is recorded rather
than started: for `K λ = ⟨g⟩` with `g` loxodromic, `fun i => g ^ i` is a
`(K,C)`-quasi-geodesic in the sense of `Hyperbolic.IsQuasiGeodesic`, and
quasiconvexity is the *chord near chain* half of `Hyperbolic.MorseLemma` --- the
named statement of `Algebra/MorseLemma.lean`, which that module already
identifies as the missing input of this lane and which nothing in the
repository assumes.  `MorseLemma` as stated gives the *chain near chord* half;
the other half follows from it together with the four-point condition and the
between-point API of `Algebra/HyperbolicSlimTriangles.lean`, by tracking the
parameters `d(p 0, q i)` of the between-points the lemma returns: consecutive
ones differ by at most `2R + K + C`, so they are `(2R + K + C)`-dense in the
interval, and two between-points at the same parameter are `2δ`-close.

Local finiteness --- clause (b) --- is the expensive half, and this module does
not touch it.  `isHyperbolicallyEmbedded_coneOffFamily_of_wordQuasiconvex`
packages the two so that the residue is exactly (b).

## Model tests

At the trivial family `K λ = ⊥`, `IsWordQuasiconvex A ⊥ 0` holds: the only
element is `1`, its geodesic word is empty, and its only prefix is `1` itself.
At `K λ = ⊤` it holds at `σ = 0` for the same reason from the other end --- every
prefix already lies in the subgroup.  At `Λ` empty the coned alphabet is Hull's
own and the conclusion is the hypothesis `hδ`, so no constant is manufactured.
And in the free group of
`GGT/HullSCConeOffHeavyProperPower.lean`, at `K λ = ⟨a²⟩` with `a` a basis
letter, it holds at `σ = 1`: a geodesic word for `a^{2m}` is a power of `a`, and
each prefix `a^j` is one letter from `a^{2⌊j/2⌋}`.  That is the right answer,
and it is the check that this reduction has not proved too much: the cone-off
along `⟨a²⟩` really is hyperbolic, and what that module refutes is clause (b),
not clause (a).  The two results are consistent.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Monotonicity of the word metric in the alphabet -/

/-- **Enlarging the alphabet cannot increase the word metric.**  This is
`WordMetric.wordNorm_mono` read at `x⁻¹ y`; it is stated here because the
cone-off argument uses it at two different pairs of points. -/
theorem wordDist_le_of_subset {G : Type u} [Group G] {S T : Set G} (hST : S ⊆ T)
    (hS : IsSymmetricGeneratingSet S) (x y : G) :
    wordDist T x y ≤ wordDist S x y := by
  unfold wordDist
  exact wordNorm_mono hST (wordLengths_nonempty hS _)

/-! ## Combinatorial quasiconvexity -/

/-- **A subgroup is `σ`-quasiconvex in `Γ(G,A)`**, in the form the cone-off
argument consumes: every prefix of an `A`-geodesic word for an element of the
subgroup lies within `σ` of the subgroup.

This is Dahmani--Guirardel--Osin's condition (b) of Theorem 4.42 --- the orbit
of the basepoint under the subgroup is quasiconvex --- written with geodesic
*words* rather than geodesic segments.  The distinction is not cosmetic: the
vertex model of a Cayley graph is not a geodesic space
(`Manuscript.NonMF.HullFillAxisDichotomy.not_isGeodesicSpace_cayley`), so a
predicate quantifying over `f : ℝ → X` with `IsGeodesicSegment f` cannot be
verified here, while this one can. -/
def IsWordQuasiconvex {G : Type u} [Group G] (A : Alphabet G) (H : Subgroup G)
    (sigma : ℕ) : Prop :=
  ∀ b ∈ H, ∀ w : List G, (∀ x ∈ w, x ∈ A.carrier) → w.prod = b →
    w.length = wordDist A.carrier 1 b →
      ∀ i ≤ w.length, ∃ e ∈ H, wordDist A.carrier (w.take i).prod e ≤ sigma

/-- **The trivial subgroup is quasiconvex at `σ = 0`.**  Recorded as the
degenerate model test: the predicate is not vacuous and not vacuously true. -/
theorem isWordQuasiconvex_bot {G : Type u} [Group G] (A : Alphabet G) :
    IsWordQuasiconvex A (⊥ : Subgroup G) 0 := by
  intro b hb w _ hprod hlen i hi
  have hb1 : b = 1 := Subgroup.mem_bot.mp hb
  refine ⟨(w.take i).prod, ?_, ?_⟩
  · have hlen0 : w.length = 0 := by
      rw [hlen, hb1, wordDist_self]
    have hi0 : i = 0 := by omega
    subst hi0
    rw [List.take_zero, List.prod_nil]
    exact one_mem _
  · rw [wordDist_self]

/-! ## Clause (a) -/

/-- **The coned-off Cayley graph is hyperbolic**, from hyperbolicity of
`Γ(G,A)` and quasiconvexity of the coned subgroups.

The whole proof is `GGT.OsinEnlargement.osinLemma55` at `M = σ + 1`.  For a
letter of `A` the geodesic word has length at most one, so every prefix is
within one of `1` in either metric; for an element of `K λ` a prefix is within
`σ` of some `e ∈ K λ` in the `A`-metric, and `e` is a letter of the coned
alphabet, so the coned distance from `1` to the prefix is at most `1 + σ`. -/
theorem exists_hyperbolic_coneOffFamily_of_wordQuasiconvex {G : Type u}
    [Group G] {Λ : Type w} (A : Alphabet G) (K : Λ → Subgroup G) {delta : ℝ}
    (hdelta : IsHyperbolicSpace delta (Cayley A)) {sigma : ℕ}
    (hqc : ∀ lam : Λ, IsWordQuasiconvex A (K lam) sigma) :
    ∃ delta' : ℝ,
      IsHyperbolicSpace delta' (Cayley (coneOffFamily A K).alphabet) := by
  have hB : (coneOffFamily A K).alphabet.carrier
      = A.carrier ∪ ⋃ lam : Λ, ((K lam : Subgroup G) : Set G) := rfl
  have hsub : A.carrier ⊆ (coneOffFamily A K).alphabet.carrier := by
    rw [hB]
    exact Set.subset_union_left
  refine GGT.OsinEnlargement.osinLemma55 G A (coneOffFamily A K).alphabet hsub
    delta hdelta (sigma + 1) ?_
  intro b hb w hwlet hwprod hwlen i hi
  have hword : IsWord A.carrier (w.take i) (w.take i).prod :=
    ⟨fun x hx => hwlet x (List.take_subset i w hx), rfl⟩
  have hpA : wordNorm A.carrier (w.take i).prod ≤ i := by
    have hle := wordNorm_le_length hword
    rw [List.length_take] at hle
    exact le_trans hle (min_le_left _ _)
  have hpB : wordNorm (coneOffFamily A K).alphabet.carrier (w.take i).prod
      ≤ wordNorm A.carrier (w.take i).prod :=
    wordNorm_mono hsub (wordLengths_nonempty A.symmetricGenerating _)
  rw [hB] at hb
  rcases hb with hbA | hbfam
  · have hb1 : wordNorm A.carrier b ≤ 1 := wordNorm_le_one_of_mem hbA
    rw [wordDist_one_left] at hwlen
    rw [wordDist_one_left]
    omega
  · obtain ⟨lam, hblam⟩ := Set.mem_iUnion.mp hbfam
    have hbK : b ∈ K lam := hblam
    obtain ⟨e, heK, hpe⟩ := hqc lam b hbK w hwlet hwprod hwlen i hi
    have heB : e ∈ (coneOffFamily A K).alphabet.carrier := by
      rw [hB]
      exact Or.inr (Set.mem_iUnion.mpr ⟨lam, heK⟩)
    have h1e : wordDist (coneOffFamily A K).alphabet.carrier 1 e ≤ 1 := by
      rw [wordDist_one_left]
      exact wordNorm_le_one_of_mem heB
    have hep : wordDist (coneOffFamily A K).alphabet.carrier e (w.take i).prod
        ≤ wordDist A.carrier e (w.take i).prod :=
      wordDist_le_of_subset hsub A.symmetricGenerating e (w.take i).prod
    have hcomm : wordDist A.carrier e (w.take i).prod
        = wordDist A.carrier (w.take i).prod e :=
      wordDist_comm A.symmetricGenerating e (w.take i).prod
    have htri := wordDist_triangle
      (coneOffFamily A K).alphabet.symmetricGenerating 1 e (w.take i).prod
    omega

/-- **The cone-off is hyperbolically embedded**, from quasiconvexity and local
finiteness.

Both clauses are named, and the point of the packaging is that after this module
the residue of the geometric leaf is clause (b) alone. -/
theorem isHyperbolicallyEmbedded_coneOffFamily_of_wordQuasiconvex {G : Type u}
    [Group G] {Λ : Type w} (A : Alphabet G) (K : Λ → Subgroup G) {delta : ℝ}
    (hdelta : IsHyperbolicSpace delta (Cayley A)) {sigma : ℕ}
    (hqc : ∀ lam : Λ, IsWordQuasiconvex A (K lam) sigma)
    (hloc : ∀ (lam : Λ) (n : ℕ), ((coneOffFamily A K).relBall lam n).Finite) :
    (coneOffFamily A K).IsHyperbolicallyEmbedded :=
  ⟨exists_hyperbolic_coneOffFamily_of_wordQuasiconvex A K hdelta hqc, hloc⟩

/-- The same over Hull's generating set, which is where the leaf is stated. -/
theorem isHyperbolicallyEmbedded_coneOffFamily_hull {G : Type u} [Group G]
    {Λ : Type w} (A : HullGeneratingSet G) (K : Λ → Subgroup G) {sigma : ℕ}
    (hqc : ∀ lam : Λ, IsWordQuasiconvex A.alphabet (K lam) sigma)
    (hloc : ∀ (lam : Λ) (n : ℕ),
      ((coneOffFamily A.alphabet K).relBall lam n).Finite) :
    (coneOffFamily A.alphabet K).IsHyperbolicallyEmbedded :=
  isHyperbolicallyEmbedded_coneOffFamily_of_wordQuasiconvex A.alphabet K
    A.hyperbolic hqc hloc

end HullSC
end GroupApproximation
