import GroupApproximation.GGT.HullSCConeOffHeavyQuasiconvex
import GroupApproximation.GGT.HullSCConeOffHeavyTransport

/-!
# Clause (a) of the cone-off leaf, packaged

`GGT.RelGenSet.IsHyperbolicallyEmbedded` has two clauses.  This module states
clause (a) — hyperbolicity of the coned-off Cayley graph — for the family the
leaf behind `Manuscript.NonMF.TorsionFree.hullHypEmbeddedConeOff` actually uses,
and reduces it to two named hypotheses and nothing else.

## The statement

`exists_hyperbolic_coneOffFamily_of_morse_of_close`: for finitely many
loxodromic elements `g λ` of a hyperbolic `Γ(G,A)` and any family `K` of
subgroups with

* `⟨g λ⟩ ≤ K λ`, and
* every element of `K λ` within `D` of `⟨g λ⟩` in the `A`-metric,

the coned-off Cayley graph `Γ(G, A ⊔ ⨆K)` is hyperbolic, given
`Hyperbolic.MorseLemma`.

At `K λ = E(g λ)` the second hypothesis is
`d_Hau(E(g λ)(1), ⟨g λ⟩(1)) < ∞`, which Dahmani--Guirardel--Osin get from
`⟨h⟩` being of finite index in `E(h)` (their Lemma 6.5, p.88).  Its honest leaf
in this repository is `GGT.Elementary.ElementaryClosureCoarseTranslation`.  At
`K λ = ⟨g λ⟩` it holds at `D = 0` and the hypothesis is free; that case is
`exists_hyperbolic_coneOffFamily_zpowers_of_morse` of
`GGT/HullSCConeOffHeavyQuasiconvex.lean`, proved there directly and not
restated here.  It is also the case the refutation of
`GGT/HullSCConeOffHeavyProperPower.lean` is consistent with: the cone-off along
`⟨a²⟩` is hyperbolic, and what a proper power fails is clause (b).

## So what clause (a) costs

Two things, both already written down elsewhere and neither of them new
mathematics: `Hyperbolic.MorseLemma` (`Algebra/MorseLemma.lean:217`) and the
bounded Hausdorff distance.  Acylindricity is not among them — it is needed for
clause (b) and for the finite index, not for hyperbolicity of the cone-off.

The chain underneath, each link a theorem of the tree: loxodromy makes the power
orbit a quasi-geodesic (`exists_isQuasiGeodesic_pow_of_isLoxodromic`); the
chord-near-chain half of the Morse lemma puts every between-point near the orbit
(`exists_index_wordDist_le_of_isBetween_of_morse`); prefixes of geodesic words
are between-points, so `⟨g⟩` is quasiconvex
(`exists_isWordQuasiconvex_zpowers_of_morse`); quasiconvexity transports across
a bounded Hausdorff distance (`isWordQuasiconvex_of_close`); and a quasiconvex
coned family leaves the Cayley graph hyperbolic, by
`GGT.OsinEnlargement.osinLemma55`
(`exists_hyperbolic_coneOffFamily_of_wordQuasiconvex`).

## What is NOT here

Clause (b), local finiteness of the relative metric.  That is
Dahmani--Guirardel--Osin's inequality (41), it needs nearest-point projections
onto the cosets and geometric separation of the family, and no part of it is
touched by this lane.  It is the remaining cost of the row.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## Weakening the quasiconvexity constant -/

/-- The predicate weakens as its constant grows, which is what lets finitely
many indices be served by one constant. -/
theorem isWordQuasiconvex_mono {G : Type} [Group G] {A : Alphabet G}
    {H : Subgroup G} {sigma sigma' : ℕ} (hsigma : sigma ≤ sigma')
    (hqc : IsWordQuasiconvex A H sigma) : IsWordQuasiconvex A H sigma' := by
  intro b hb w hlet hprod hlen i hi
  obtain ⟨e, he, hle⟩ := hqc b hb w hlet hprod hlen i hi
  exact ⟨e, he, le_trans hle hsigma⟩

/-! ## Clause (a) -/

/-- **Clause (a) of the cone-off leaf**, for a family sandwiched between the
cyclic subgroups of loxodromic elements and a bounded neighbourhood of them.

See the module header for what the two hypotheses are and for the chain of
theorems underneath.  The constant is `sup σ + 2D + 4⌈δ⌉₊`, where `σ λ` is the
quasiconvexity constant of `⟨g λ⟩` that the Morse lemma supplies. -/
theorem exists_hyperbolic_coneOffFamily_of_morse_of_close
    (hmorse : Hyperbolic.MorseLemma) {G : Type} [Group G] {Λ : Type} [Fintype Λ]
    (A : Alphabet G) {delta : ℝ} (hdelta : IsHyperbolicSpace delta (Cayley A))
    (g : Λ → G) (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A))
    (K : Λ → Subgroup G) (hzle : ∀ lam : Λ, Subgroup.zpowers (g lam) ≤ K lam)
    (D : ℕ) (hclose : ∀ lam : Λ, ∀ b ∈ K lam,
      ∃ b' ∈ Subgroup.zpowers (g lam), wordDist A.carrier b b' ≤ D) :
    ∃ delta' : ℝ, IsHyperbolicSpace delta' (Cayley (coneOffFamily A K).alphabet) := by
  have h4 : Hyperbolic.IsFourPointHyperbolic A.carrier ⌈delta⌉₊ :=
    GGT.isFourPointHyperbolic_of_isHyperbolicSpace_cayley A hdelta
  have hqc : ∀ lam : Λ, ∃ sigma : ℕ,
      IsWordQuasiconvex A (Subgroup.zpowers (g lam)) sigma := fun lam =>
    exists_isWordQuasiconvex_zpowers_of_morse hmorse A h4 (hlox lam)
  choose sigma hsigma using hqc
  refine exists_hyperbolic_coneOffFamily_of_wordQuasiconvex A K hdelta
    (sigma := Finset.univ.sup sigma + 2 * D + 4 * ⌈delta⌉₊) ?_
  intro lam
  have hstep : IsWordQuasiconvex A (K lam) (sigma lam + 2 * D + 4 * ⌈delta⌉₊) :=
    isWordQuasiconvex_of_close A h4 (hzle lam) (hclose lam) (hsigma lam)
  refine isWordQuasiconvex_mono ?_ hstep
  have hsup : sigma lam ≤ Finset.univ.sup sigma :=
    Finset.le_sup (f := sigma) (Finset.mem_univ lam)
  omega

end HullSC
end GroupApproximation
