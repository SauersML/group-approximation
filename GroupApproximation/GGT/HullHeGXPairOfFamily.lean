import GroupApproximation.GGT.HullHeGXFamily
import GroupApproximation.GGT.HullYiStatements
import GroupApproximation.GGT.HullEeOneStep

/-!
# `HeGXPair` is `HeGXFamily` at two indices

`GGT.HeGXFamily` states Hull's Corollary `heGX` over a finite index type, and
`HullSC.HeGXPair` is what the two-subgroup cone-off consumes.  This module
derives the second from the first, so nothing is owed between them.

**A single-subgroup form could not have served here**, and that is worth
recording where the derivation lives: `HullSC.not_isHyperbolicallyEmbedded_elementaryClosure_conj`
proves `{E(f), E(c f c⁻¹)}` is never hyperbolically embedded, while both members
satisfy a single-subgroup hypothesis individually, a conjugate of a loxodromic
being loxodromic.  So two instances of a one-element statement cannot give the
pair, and what separates two indices is non-commensurability — which at one
element has nothing to say.  That is why the primary form is a family.

## What the derivation costs

Three things, none of them deep.

* **A relative generating set with no peripheral family.**  `HeGXFamily` is
  stated over a `RelGenSet` because Hull's Lemma `ee` needs it at the alphabet
  Osin's Theorem 5.4 hands back; `HeGXPair` starts from a bare
  `HullGeneratingSet`, since Hull's `heGX` has no pre-existing hyperbolically
  embedded family.  The honest instantiation is therefore the empty index type,
  and no new constructor is needed: `coneOffFamily A Empty.elim` already **is**
  the relative generating set with base `A` and no family, `coneOffFamily`
  being general in its index.
* **The alphabet equality, which is only propositional.**  `RelGenSet.alphabet`
  is `⟨base ∪ ⋃ lam, fam lam, _⟩`, so the empty cone-off has carrier
  `A.carrier ∪ ⋃ (e : Empty), _`, equal to `A.carrier` by `Set.iUnion_of_empty`
  and `Set.union_empty` but not definitionally.
  `GGT.OsinComponents.alphabet_eq_of_carrier_eq` lifts that to the alphabets,
  the generating clause being a proposition.
* **Transfer rather than rewriting.**  The alphabet occurs in a type and in an
  instance, so a `rw` of the equality can fail on the motive.  Each hypothesis
  crosses instead by a lemma stated over two *free* alphabets and closed by
  `subst`, which is the shape `GGT.hyperbolic_of_alphabet_eq` already uses.
  `Cayley` itself is not an obstacle: it ignores its alphabet argument, so the
  underlying type never moves and only the pseudometric instance does.

## The clause that is not free

`HeGXFamily` asks non-commensurability at every ordered pair `i ≠ j`, while
`HeGXPair` carries only the `(false, true)` direction.  The other direction is
recovered by inverting the conjugator: from `c⁻¹ (g true)^p c = (g false)^q` one
gets `(c⁻¹)⁻¹ (g false)^q c⁻¹ = (g true)^p`, which is the given clause at
`(c⁻¹, q, p)`.  So the pair form carries the weaker-looking hypothesis without
loss.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G]

/-! ## The empty cone-off, and crossing its alphabet equality -/

/-- **Coning off the empty family changes nothing.**  The base is `A` by
construction and the family contributes an empty union. -/
theorem alphabet_coneOffFamily_empty (A : Alphabet G) :
    (coneOffFamily A (Empty.elim : Empty → Subgroup G)).alphabet = A := by
  refine GGT.OsinComponents.alphabet_eq_of_carrier_eq ?_
  show A.carrier ∪ ⋃ e : Empty, ((Empty.elim e : Subgroup G) : Set G)
    = A.carrier
  rw [Set.iUnion_of_empty, Set.union_empty]

/-- Acylindricity crosses an alphabet equality. -/
theorem isAcylindrical_of_alphabet_eq {A₁ A₂ : Alphabet G} (h : A₁ = A₂)
    (ha : IsAcylindrical G (Cayley A₂)) : IsAcylindrical G (Cayley A₁) := by
  subst h
  exact ha

/-- Loxodromy crosses an alphabet equality. -/
theorem isLoxodromic_of_alphabet_eq {A₁ A₂ : Alphabet G} (h : A₁ = A₂) {x : G}
    (hx : IsLoxodromic x (Cayley.base A₂)) :
    IsLoxodromic x (Cayley.base A₁) := by
  subst h
  exact hx

/-- A hyperbolically embedded cone-off crosses an alphabet equality. -/
theorem isHyperbolicallyEmbedded_coneOffFamily_of_alphabet_eq
    {A₁ A₂ : Alphabet G} (h : A₁ = A₂) {K : Bool → Subgroup G}
    (he : (coneOffFamily A₁ K).IsHyperbolicallyEmbedded) :
    (coneOffFamily A₂ K).IsHyperbolicallyEmbedded := by
  subst h
  exact he

/-! ## The derivation -/

/-- **`HeGXPair` is `HeGXFamily` at `ι = Bool`.**

The family is coned off over the empty index, the four hypotheses cross the
alphabet equality by `subst`, and the missing direction of non-commensurability
comes from inverting the conjugator. -/
theorem heGXPair_of_heGXFamily (hfam : GGT.HeGXFamily.{u, 0}) :
    HeGXPair.{u} := by
  intro G _ A g hlox hnc
  have halph := alphabet_coneOffFamily_empty A.alphabet
  have hemb : (coneOffFamily A.alphabet
      (Empty.elim : Empty → Subgroup G)).IsHyperbolicallyEmbedded :=
    { hyperbolic := GGT.hyperbolic_of_alphabet_eq halph ⟨A.delta, A.hyperbolic⟩
      locallyFinite := fun lam => lam.elim }
  have hacyl : IsAcylindrical G (Cayley (coneOffFamily A.alphabet
      (Empty.elim : Empty → Subgroup G)).alphabet) :=
    isAcylindrical_of_alphabet_eq halph A.acylindrical
  have hloxD : ∀ b : Bool, IsLoxodromic (g b)
      (Cayley.base (coneOffFamily A.alphabet
        (Empty.elim : Empty → Subgroup G)).alphabet) :=
    fun b => isLoxodromic_of_alphabet_eq halph (hlox b)
  have hncD : ∀ i j : Bool, i ≠ j → ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
      c⁻¹ * g i ^ p * c ≠ g j ^ q := by
    intro i j hij c p q hp hq
    cases i with
    | false =>
        cases j with
        | false => exact absurd rfl hij
        | true => exact hnc c p q hp hq
    | true =>
        cases j with
        | false =>
            intro hcon
            refine hnc c⁻¹ q p hq hp ?_
            rw [inv_inv, ← hcon]
            group
        | true => exact absurd rfl hij
  exact isHyperbolicallyEmbedded_coneOffFamily_of_alphabet_eq halph
    (hfam G Empty (coneOffFamily A.alphabet (Empty.elim : Empty → Subgroup G))
      hemb hacyl Bool g hloxD hncD)

end HullSC
end GroupApproximation
