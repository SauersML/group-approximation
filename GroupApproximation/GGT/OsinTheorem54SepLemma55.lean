import GroupApproximation.GGT.OsinTheorem54Family

/-!
# Osin's Lemma 5.5, declared as a debt

**This module declares an unproved statement.**  It is here because `emb` ---
clause (a) of Theorem 5.4, the hyperbolicity of `Γ(G, Y ⊔ ℋ)` --- cannot be
reached without it, and because the shape of the debt is worth pinning down
even though the proof is not being attempted.  Everything known about it is
recorded below so that nobody re-derives it.

## The statement

`OsinLemma55` says: enlarging an alphabet preserves hyperbolicity when every
old geodesic joining the endpoints of a new letter stays within bounded
distance, *measured in the new metric*, of the basepoint.  That is Osin's
Lemma 5.5, which he states without proof as Corollary 2.4 of Kapovich--Rafi.

`GGT/OsinLemma55GuessingGeodesics.lean` proves it from Bowditch's
guessing-geodesics criterion, which it declares in its place; what is left
unproved is that criterion and nothing else.

For a letter already in the old alphabet the old geodesic has length one and
the condition is free, so the hypothesis bites only on the new letters.

## Model tests

*Positive.*  `G = ℤ`, `A = {t^±1}`, `B = A ∪ {t^±2, t^±3}`.  The `A`-geodesic to
`t³` has prefix vertices `1, t, t², t³`, each at `B`-distance one, so `M = 1`;
and `Γ(ℤ, B)` is quasi-isometric to the line, hence hyperbolic.  Hypothesis
holds, conclusion holds.

*The lemma cannot manufacture hyperbolicity.*  Hyperbolicity of the SMALLER
graph is a hypothesis.  For `ℤ²` with the standard generators `Cayley A` is the
grid and `IsHyperbolicSpace δ` fails for every `δ`, so the lemma says nothing
about any enlargement of it.  `ℤ²` is excluded at the hypothesis, which is where
it should be excluded.

## The naive proof route is refuted

One is tempted to say that Gromov products move by at most the diameter bound,
and to transport the four-point inequality across.  **That is false.**  Take
`G = ℤ`, `A = {t^±1}`, `B` all of `ℤ`; then `M = 1`, since every element is a
letter.  But `(t^n | t^{2n})_1` is `n` in the `A`-metric and `1/2` in the
`B`-metric: the gap grows without bound while `M` stays at one.  The reason is
structural --- the whole point of an enlargement is that `d_B` is much *smaller*
than `d_A`, so the two are nowhere near bounded distance and the four-point
condition for one is not a perturbation of the other.  Any route that transports
the inequality with a bounded error dies on this example.

The statement survives it: `Γ(ℤ, ℤ)` has diameter one and is hyperbolic.  The
example refutes the route, not the lemma.

## What it would cost

`Γ(G,B)` is `Γ(G,A)` with a family of subsets coned off --- the `A`-geodesics of
the new letters and their translates --- and the hypothesis says that family is
uniformly bounded in the coned metric.  So this is an instance of "coning off a
uniformly quasiconvex family in a hyperbolic space leaves it hyperbolic"
(Bowditch; Kapovich--Rafi), whose proof runs through thin triangles in the coned
space.  Starting from the four-point condition, with no geodesic-space API
beyond what this repository has, that is of the same order as the §4.2
isolated-component bound.

## An open routing question

Theorem 5.4's consumer is `(AH₄) ⇒ (AH₁)`, which needs *some* `Y` that is both
`↪_h` and acylindrical --- not specifically Osin's `Y = {y | S(1,y;D) = ∅}`.
Whether the chain can be routed around Lemma 5.5 by choosing a different
enlargement is open, and is a question about the whole chain rather than about
this module.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **Osin, Lemma 5.5** (Kapovich--Rafi, Corollary 2.4), **unproved here**.

Enlarging an alphabet preserves hyperbolicity when the old geodesics joining the
endpoints of the new letters stay within bounded distance of the basepoint in
the *new* metric.  See the module header for the model tests, the refutation of
the naive proof route, and the cost estimate. -/
def OsinLemma55 : Prop :=
  ∀ (G : Type u) [Group G] (A B : Alphabet G), A.carrier ⊆ B.carrier →
    ∀ δ : ℝ, IsHyperbolicSpace δ (Cayley A) →
      ∀ M : ℕ,
        (∀ b ∈ B.carrier, ∀ w : List G, (∀ x ∈ w, x ∈ A.carrier) →
          w.prod = b → w.length = wordDist A.carrier 1 b →
          ∀ i ≤ w.length, wordDist B.carrier 1 (w.take i).prod ≤ M) →
        ∃ δ' : ℝ, IsHyperbolicSpace δ' (Cayley B)

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Clause (a) of Theorem 5.4 from Lemma 5.5**, with its two other inputs as
explicit binders rather than named leaves.

`hM` is the content of Osin's Lemma 5.6 --- that his `Y` satisfies the
bounded-detour condition --- and `hloc` is his Lemma 5.8, the local finiteness
of `d̂_λ` over the enlarged base.  Neither is supplied here.  `hloc` is not
reachable from `OsinComponents.relBall_finite_of_base_subset'`, which needs the
added letters to be finite and inside the family, and `Y \ X` is neither; nor
from `GGT.DGOCorollary427`, whose own docstring records that it does not license
this passage, the enlargement being infinite.

So `emb` rests on three inputs, of which this module declares one. -/
theorem isHyperbolicallyEmbedded_of_lemma55 (h55 : OsinLemma55.{u})
    (D D' : RelGenSet G Λ) (hemb : D.IsHyperbolicallyEmbedded)
    (hsub : D.alphabet.carrier ⊆ D'.alphabet.carrier)
    (hM : ∃ M : ℕ, ∀ b ∈ D'.alphabet.carrier, ∀ w : List G,
      (∀ x ∈ w, x ∈ D.alphabet.carrier) → w.prod = b →
      w.length = wordDist D.alphabet.carrier 1 b →
      ∀ i ≤ w.length, wordDist D'.alphabet.carrier 1 (w.take i).prod ≤ M)
    (hloc : ∀ (lam : Λ) (n : ℕ), (D'.relBall lam n).Finite) :
    D'.IsHyperbolicallyEmbedded := by
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  obtain ⟨M, hMs⟩ := hM
  exact ⟨h55 G D.alphabet D'.alphabet hsub δ hδ M hMs, hloc⟩

end OsinEnlargement
end GGT
end GroupApproximation
