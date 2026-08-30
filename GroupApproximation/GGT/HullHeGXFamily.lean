import GroupApproximation.GGT.HullLemmaEe
import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

/-!
# Hull's Corollary `heGX` at a family, and why the single form is not enough

Hull, *Small cancellation in acylindrically hyperbolic groups* (arXiv:1308.4345),
Corollary `heGX`, is stated at a **family**:

> Suppose `X` is a generating set of `G` such that `Γ(G, X)` is hyperbolic and
> `{g₁,…,g_n}` is a collection of pairwise non-commensurable loxodromic WPD
> elements with respect to the action of `G` on `Γ(G, X)`.  Then
> `{E_G(g₁),…,E_G(g_n)} ↪_h (G, X)`.

`GGT/HullLemmaEe.lean` states `HeGXSingle`, the case `n = 1`, because that is all
Hull's Lemma `ee` reads.  This module states the family form and derives the
single form from it.

## The single form does NOT imply the pair form, and that is a theorem

It was recorded for a while that `HeGXSingle` was the primary citation, with
`HullSC.HeGXPair` its instance at `n = 2` and a bridge owed by whoever discharged
either.  **There is no such bridge, and there cannot be one.**

`HullSC.not_isHyperbolicallyEmbedded_elementaryClosure_conj`
(`GGT/HullYiNonCommensurable.lean`) proves that for a loxodromic `f` and any `c`,
a family with members `E(f)` and `E(c f c⁻¹)` is **never** hyperbolically
embedded.  Both members satisfy the hypotheses of `HeGXSingle` separately ---
`c f c⁻¹` is loxodromic whenever `f` is, `IsLoxodromic` carrying the additive
constant that makes it invariant under conjugation --- and yet the pair provably
fails.  So no argument takes two instances of the single form to the pair form,
and the missing content is exactly the hypothesis the single form has no room to
state: **non-commensurability is a relation between two indices, and at one index
there is nothing for it to say.**

That is why the family form is the primary citation and the single form is a
consequence of it rather than the other way round.

## Non-commensurability is carried in the conjugate form

`∀ c p q, p ≠ 0 → q ≠ 0 → c⁻¹ * aᵢ ^ p * c ≠ a_j ^ q`, and not the weak
`∀ p q, aᵢ ^ p ≠ a_j ^ q`.  The same witness forces this: `f` and `c f c⁻¹`
satisfy the weak clause whenever no power of one is literally a power of the
other, so a family form carrying the weak clause would be refuted by the
very theorem above.  The conjugator is not decoration.

## What this costs the two consumers

Nothing.  Lemma `ee` continues to read `HeGXSingle`, which
`heGXSingle_of_heGXFamily` now supplies, so `GGT/HullLemmaEe.lean` is untouched;
its non-commensurability obligation is vacuous because `Unit` has one index.  The
pair form is this statement at `ι = Bool`, where the clause is exactly the one
`HullSC.HeGXPair` already carries.  Both are instances of one citation, which is
what the earlier arrangement was reaching for and could not have.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.HullSC
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **Hull's Corollary `heGX`** (Dahmani--Guirardel--Osin, Theorem 6.8): the
elementary closures of finitely many pairwise non-commensurable loxodromic
elements are hyperbolically embedded over the prescribed alphabet.

Acylindricity stands in for WPD, absorbing Hull's step *"since the action is
acylindrical, all loxodromic elements satisfy WPD"*, for which this repository
has no theorem.

The index type is `Type` rather than a universe variable because every consumer
indexes by `Unit` or `Bool`, and `IsHypEmbeddedOf` --- the shape the single form
concludes in --- pins its family at `Unit` anyway. -/
def HeGXFamily : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → IsAcylindrical G (Cayley D.alphabet) →
      ∀ (ι : Type) [Finite ι] (a : ι → G),
        (∀ i : ι, IsLoxodromic (a i) (Cayley.base D.alphabet)) →
          (∀ i j : ι, i ≠ j → ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
            c⁻¹ * a i ^ p * c ≠ a j ^ q) →
            (coneOffFamily D.alphabet
              (fun i => elementaryClosure (a i))).IsHyperbolicallyEmbedded

/-- **The single form is the family form at one index.**

The non-commensurability hypothesis discharges itself: `Unit` has one element, so
`i ≠ j` is uninhabited and there is no pair to be commensurable.  This is the
direction that exists; the converse does not, for the reason in the module
header. -/
theorem heGXSingle_of_heGXFamily (h : HeGXFamily.{u, w}) : HeGXSingle.{u, w} := by
  intro G _instG Λ D hD hacy a hlox
  refine ⟨coneOffFamily D.alphabet (fun _ : Unit => elementaryClosure a),
    rfl, rfl, ?_⟩
  exact h G Λ D hD hacy Unit (fun _ => a) (fun _ => hlox)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)

end GGT
end GroupApproximation
