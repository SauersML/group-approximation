import GroupApproximation.GGT.HullSCRelatorSeparation2Core
import GroupApproximation.GGT.DGOCorollary427PairLocal

/-!
# Adjoining Hull's stable letter to the base of the two-subgroup core

Hull, *Small cancellation in acylindrically hyperbolic groups*
(arXiv:1308.4345), Theorem 5.1, reads his relator in

    𝒜₁ = (𝒜 ∪ {t^{±1}}) ⊔ ⟨h₁⟩ ⊔ ⟨h₂⟩

adjoining `t` to the alphabet **as a letter**, so that the relator carries one
`X`-letter and is a `W`-word.  His `suitsubc` produces the embedding over `𝒜`,
not over the enlargement; the step between them is Dahmani--Guirardel--Osin's
**Corollary 4.27**, invariance of `↪_h` under a finite symmetric difference of
the base, which they perform in these words: *"By Corollary 4.27 we can assume
that `t ∈ X` without loss of generality."*  Its one-pair relative-metric
content is proved directly in `DGOCorollary427PairLocal`, so this module no
longer takes the full cited equivalence as a premise.

This module is that step at `HypEmbeddedCore₂`.

## What moves and what does not

Only the base moves.  `HullSC.ExistsHypEmbeddedConeOff₂` stays over the
un-enlarged alphabet, matching what Hull's §5 proves in one step, and the
enlargement is owed here at the consumer where it is visible.  Of the core's
eleven fields, **eight are carried over verbatim**: the family, its containment
in `N`, the two loxodromic elements, their membership, their loxodromy and the
trivial intersection are all unchanged, because none of them mentions the base.

In particular `lox_isLoxodromic` stays indexed on `Cayley.base A.alphabet`.
That clause would be endangered if it were restated over the enlarged base ---
enlarging a generating set only shrinks distances, and nothing becomes *more*
loxodromic --- but it is not restated, and it does not need to be: the two
places the chain spends it, `injective_pow_lox₂` and `H_ne_of_disjoint₂`, go
through `not_isOfFinOrder_of_isLoxodromic`, and infinite order does not depend
on the base at all.

The three fields that do change are `rel`, `base_le` and `base_inv`, and the
last two are free: containment is transitivity through
`RelGenSet.base_subset_adjoinPair`, and inversion-closure is the old base's
closure together with the fact that `t` and `t⁻¹` are adjoined **together**.
The generating half of symmetry is not a field at all --- a superset of a
generating set generates, which is `HullSC.isSymmetricGeneratingSet_base₂`.

## What it unblocks

Putting `t⁻¹` into the base is what the one-letter spelling `p = [t⁻¹]` needs,
and that spelling is what makes the relator carry a single `X`-letter, so that
Dahmani--Guirardel--Osin's (W1) and (W4) hold of the whole word rather than of
its run-internal pieces only.  That is the base-crossing gap of the separation
chain.  The one-pair case is proved by the fixed-spelling expansion in
`DGOCorollary427PairLocal`.

**Two things this module does not by itself deliver**, recorded so that no
reader takes the gap for closed:

* Membership is necessary but not sufficient for the short spelling.
  `exists_base_spelling_of_base_le` spells `t⁻¹` over `A.alphabet.carrier` and
  only then pushes its letters into the larger base, so it returns an
  `𝒜`-spelling however large the base is.  A singleton lemma --- a letter of the
  base is spelled by itself --- is what converts membership into `|p| = 1`, and
  it belongs beside that spelling lemma rather than here.
* `HullRelatorStatement₂` fixes the core **before** `t`, while the core built
  here depends on `t`.  A small-cancellation conclusion at
  `E.adjoinPair t` is a different claim from one at `E`, because it is
  measured in the enlarged relative metric.  The repaired seam
  `hullOneStep_of_quotient₂_of_baseLetter` introduces `t`, constructs the
  enlarged core, and invokes `HullRelatorStatement₂OfBaseLetter` there.  The
  quotient half is invoked on that same core; nothing is transferred back to
  `E`.  This module supplies the core and no more.

The same `DGOCorollary427` is what Hull's `nonelsub` needs for its first
application of Lemma `lox`, where the element from Theorem `subah` is spelled by
two or more base letters and so fails (W1); see
`GGT/HullYiStatements.lean`.  One citation, two consumers.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The enlarged base is closed under inversion.**  The old base is, by the
core's own field, and `t` and `t⁻¹` are adjoined together. -/
theorem base_inv_adjoinPair (E : HypEmbeddedCore₂ A N) (t : G) :
    ∀ x ∈ (E.rel.adjoinPair t).base, x⁻¹ ∈ (E.rel.adjoinPair t).base := by
  intro x hx
  simp only [GGT.RelGenSet.adjoinPair_base, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx ⊢
  rcases hx with hx | rfl | rfl
  · exact Or.inl (E.base_inv x hx)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (inv_inv t))

/-- **Hull's `𝒜₁`, at the core.**

Given the two-subgroup core over Hull's alphabet, the same core over
`𝒜 ∪ {t^{±1}}`.  Pair-local finiteness and the hyperbolicity transport are
proved in the two `DGOCorollary427FiniteExtension` modules.  Everything but the
base is carried over unchanged; see the module header for why
`lox_isLoxodromic` in particular survives untouched. -/
def HypEmbeddedCore₂.adjoinPair (E : HypEmbeddedCore₂ A N)
    (t : G) : HypEmbeddedCore₂ A N where
  rel := E.rel.adjoinPair t
  base_le := E.base_le.trans (GGT.RelGenSet.base_subset_adjoinPair E.rel t)
  base_inv := base_inv_adjoinPair E t
  H := E.H
  fam_eq := E.fam_eq
  le := E.le
  embedded := GGT.RelGenSet.isHyperbolicallyEmbedded_adjoinPair_of_localFiniteness
    GGT.RelGenSet.pairLocalFiniteness E.rel E.embedded t
  lox := E.lox
  lox_mem := E.lox_mem
  lox_isLoxodromic := E.lox_isLoxodromic
  disjoint := E.disjoint

/-- The enlarged core's base contains the adjoined letter, which is the whole
point: `t⁻¹` is spelled by one letter rather than by a word over `𝒜`. -/
theorem mem_base_adjoinPair (E : HypEmbeddedCore₂ A N)
    (t : G) : t⁻¹ ∈ (E.adjoinPair t).rel.base := by
  show t⁻¹ ∈ E.rel.base ∪ {t, t⁻¹}
  exact Or.inr (Or.inr rfl)

end HullSC
end GroupApproximation
