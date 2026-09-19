import GroupApproximation.GGT.HullSCConeOffHeavyModel
import GroupApproximation.GGT.HullSCConeOffHeavyTransport

/-!
# Clause (a) of the cone-off leaf, unconditionally

`GGT/HullSCConeOffHeavyClauseA.lean` states clause (a) — hyperbolicity of the
coned-off Cayley graph — modulo `Hyperbolic.MorseLemma` and a bounded Hausdorff
distance.  `GGT/HullSCConeOffHeavyModel.lean` removes the first of those by
proving quasiconvexity through the geodesic model instead.  This module composes
them, so clause (a) rests on the Hausdorff bound alone.

## The statement

`exists_hyperbolic_coneOffFamily_of_close`: for finitely many loxodromic
elements `g λ` of `Γ(G,A)` and any family `K` of subgroups with `⟨g λ⟩ ≤ K λ` and
every element of `K λ` within `D` of `⟨g λ⟩`, the graph `Γ(G, A ⊔ ⨆K)` is
hyperbolic.  No `MorseLemma`, no acylindricity beyond what `HullGeneratingSet`
already carries, and no universe restriction — the Morse-conditional route was
confined to `Type` because `Hyperbolic.MorseLemma` is, and this one is not.

At `K λ = E(g λ)` the hypothesis is Dahmani--Guirardel--Osin's
`d_Hau(E(h)(s), ⟨h⟩(s)) < ∞` (their Lemma 6.5), whose leaf here is
`GGT.Elementary.ElementaryClosureCoarseTranslation`.  At `K λ = ⟨g λ⟩` it holds
at `D = 0`, and `exists_hyperbolic_coneOffFamily_zpowers` below is that case.

## What remains of the row

Clause (b), local finiteness of the relative metric — Dahmani--Guirardel--Osin's
inequality (41).  Nothing in this lane touches it, and it needs nearest-point
projections onto the cosets together with geometric separation of the family,
neither of which the tree has.

## A note on the two routes

The Morse-conditional chain of `GGT/HullSCConeOffHeavyQuasiconvex.lean` is not
superseded: it is stated at an abstract four-point-hyperbolic alphabet, where no
geodesic model is available, while this route needs a `HullGeneratingSet`.  Its
universe-zero copy of `isWordQuasiconvex_mono` is superseded, though;
`isWordQuasiconvex_of_le` below is the same statement at a general universe, and
the two should be unified when the Morse route is retired.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- The quasiconvexity predicate weakens as its constant grows.  This is
`isWordQuasiconvex_mono` of `GGT/HullSCConeOffHeavyClauseA.lean` at a general
universe. -/
theorem isWordQuasiconvex_of_le {G : Type u} [Group G] {A : Alphabet G}
    {H : Subgroup G} {sigma sigma' : ℕ} (hsigma : sigma ≤ sigma')
    (hqc : IsWordQuasiconvex A H sigma) : IsWordQuasiconvex A H sigma' := by
  intro b hb w hlet hprod hlen i hi
  obtain ⟨e, he, hle⟩ := hqc b hb w hlet hprod hlen i hi
  exact ⟨e, he, le_trans hle hsigma⟩

/-! ## Clause (a), unconditionally -/

/-- **Clause (a) of the cone-off leaf, with no Morse hypothesis.**

The quasiconvexity of each `⟨g λ⟩` comes from
`exists_isWordQuasiconvex_zpowers`, which is proved in the geodesic model;
`isWordQuasiconvex_of_close` carries it to `K λ`; and
`exists_hyperbolic_coneOffFamily_of_wordQuasiconvex` — that is,
`GGT.OsinEnlargement.osinLemma55` — turns it into hyperbolicity of the
cone-off. -/
theorem exists_hyperbolic_coneOffFamily_of_close {G : Type u} [Group G]
    {Λ : Type w} [Fintype Λ] (A : HullGeneratingSet G) (g : Λ → G)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A.alphabet))
    (K : Λ → Subgroup G) (hzle : ∀ lam : Λ, Subgroup.zpowers (g lam) ≤ K lam)
    (D : ℕ) (hclose : ∀ lam : Λ, ∀ b ∈ K lam,
      ∃ b' ∈ Subgroup.zpowers (g lam), wordDist A.alphabet.carrier b b' ≤ D) :
    ∃ delta' : ℝ,
      IsHyperbolicSpace delta' (Cayley (coneOffFamily A.alphabet K).alphabet) := by
  have h4 : Hyperbolic.IsFourPointHyperbolic A.alphabet.carrier ⌈A.delta⌉₊ :=
    GGT.isFourPointHyperbolic_of_isHyperbolicSpace_cayley A.alphabet A.hyperbolic
  have hqc : ∀ lam : Λ, ∃ sigma : ℕ,
      IsWordQuasiconvex A.alphabet (Subgroup.zpowers (g lam)) sigma := fun lam =>
    exists_isWordQuasiconvex_zpowers A (hlox lam)
  choose sigma hsigma using hqc
  refine exists_hyperbolic_coneOffFamily_of_wordQuasiconvex A.alphabet K
    A.hyperbolic (sigma := Finset.univ.sup sigma + 2 * D + 4 * ⌈A.delta⌉₊) ?_
  intro lam
  have hstep : IsWordQuasiconvex A.alphabet (K lam)
      (sigma lam + 2 * D + 4 * ⌈A.delta⌉₊) :=
    isWordQuasiconvex_of_close A.alphabet h4 (hzle lam) (hclose lam) (hsigma lam)
  refine isWordQuasiconvex_of_le ?_ hstep
  have hsup : sigma lam ≤ Finset.univ.sup sigma :=
    Finset.le_sup (f := sigma) (Finset.mem_univ lam)
  omega

/-- **The cyclic case**, where the Hausdorff hypothesis is free.

This is the form consistent with `GGT/HullSCConeOffHeavyProperPower.lean`: the
cone-off along cyclic subgroups is hyperbolic, and what a proper power fails is
clause (b), not clause (a). -/
theorem exists_hyperbolic_coneOffFamily_zpowers {G : Type u} [Group G]
    {Λ : Type w} [Fintype Λ] (A : HullGeneratingSet G) (g : Λ → G)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A.alphabet)) :
    ∃ delta' : ℝ, IsHyperbolicSpace delta'
      (Cayley (coneOffFamily A.alphabet
        (fun lam => Subgroup.zpowers (g lam))).alphabet) :=
  exists_hyperbolic_coneOffFamily_of_close A g hlox
    (fun lam => Subgroup.zpowers (g lam)) (fun _ => le_refl _) 0
    (fun _ b hb => ⟨b, hb, by rw [wordDist_self]⟩)

end HullSC
end GroupApproximation
