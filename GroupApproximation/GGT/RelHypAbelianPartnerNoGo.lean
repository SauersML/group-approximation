import GroupApproximation.Sofic.OsinWeightedMetric

/-!
# A weighted design with an abelian partner refutes the Greendlinger leaf

**Read this before attacking `WeightedGreendlingerLeaf`, and before consuming
`GGT.RelHyp.OsinTheorem24` as stated.**

`OsinWeightedMetric.WeightedRouterDesign` proves, with no leaf spent, that the
partner factor surjects onto the routed quotient
(`partnerHom_surjective` — that is what the `tie` field buys).  So if the
partner factor is **abelian**, the routed quotient is abelian, and every
commutator of the source factor dies in it.  A dead commutator of the source is
a nonidentity element of the relator subgroup whose *relative* length is at most
one, by the peripheral clause `len_source_le_one`.  And an element of the
relator subgroup of relative length one refutes `RelativeLengthBound` against
any family with relators of two letters or more — which is
`OsinWeightedMetric.not_relativeLengthBound_of_short`, already in the tree.

So: **a weighted router design with a nonabelian source factor and an abelian
partner factor makes `WeightedGreendlingerLeaf` false at its own relator
family.**  That is `not_relativeLengthBound_of_abelian_partner` below.

## What this means for the lane, and it is not small

`GGT/RelHypOsinTheorem24.lean` defines

    OsinTheorem24 := ∀ G _ L R lam,
      WeightedGreendlingerLeaf L R lam ∧ WeightedTorsionLeaf L R lam

as the universal closure of the two leaves.  The theorem below says that
universal closure is **false as soon as some weighted router design exists with
a nonabelian source and an abelian partner**.  Nothing in the six design
certificates — finite, symmetrized, letter-reduced, letters, the 42-letter
floor, `C'(1/8)`, and the tie — mentions the partner factor's geometry at all,
so nothing in them visibly rules such a design out.  Two possibilities, and the
lane needs to know which:

* **Such a design does not exist.**  Then the certificates secretly exclude
  abelian partners, and the proof of `WeightedGreendlingerLeaf` must find and
  use that fact.  Whoever proves the leaf is proving, en route, that the
  certificates are unsatisfiable over an abelian partner — so a proof that never
  looks at the partner is wrong.
* **Such a design exists.**  Then the leaf is false, `OsinTheorem24` must be
  restricted (the natural restriction being to designs whose partner factor is
  non-elementary, which is exactly the hypothesis
  `RelHyp.OsinRelatorDesign` already carries and which the leaf does not), and
  every consumer of the unrestricted form has to be re-pointed.

The author's own reading is that the second is more likely, because
`LetterIsPiece` is a *literal common prefix of letter lists*, whereas Osin's
piece is equality of subwords **in the group** up to a bounded correction —
a strictly broader notion, invisible to a condition stated on lists.  A family
whose letters are pairwise distinct has no literal pieces at all and satisfies
`LetterMetricSmallCancellation` at every constant, vacuously, however badly its
paths fellow-travel.  `GGT/RelHypLetterPieces.lean` makes that vacuity into a
one-line theorem, which is useful if the leaf is true and is the shape of a
counterexample if it is not.

Either way the resolution is cheap to state and expensive to guess, so it is
stated rather than guessed.

## Why the manuscript's own application is not in danger

`RelHyp.OsinRelatorDesign` requires `IsNonElementaryHyperbolic H`, and an
abelian torsion-free hyperbolic group is elementary, so the manuscript's `H₀` is
never abelian and the no-go below never fires against the Fournier-Facio
construction.  The problem is confined to the *universally quantified* form of
the leaf, which is stronger than that application needs.  This is the same
lesson as the `ℤ`/`F₂` separation recorded in `GGT/RelHypOsinTheorem24.lean`:
non-elementarity of the partner factor is load-bearing, and a statement that
does not mention it is claiming too much.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open OsinWeightedMetric
open scoped commutatorElement

/-! ## 1.  A dead source commutator refutes the length bound -/

/-- **A commutator of the source factor that dies in the quotient refutes the
length bound.**

The element is peripheral, so its relative length is at most one by
`len_source_le_one`; the floor makes every relator at least two letters; and
`not_relativeLengthBound_of_short` does the rest.  Nothing here is about
designs: it is the sharpest form of the obstruction, at an arbitrary relator
family. -/
theorem not_relativeLengthBound_of_dead_commutator {G : Bool → Type}
    [∀ b, Group (G b)] {R : Set (List (CoprodI G))} {L : RelativeLength G}
    {x y : G false} (hxy : x * y ≠ y * x) (hfloor : ∀ r ∈ R, 2 ≤ r.length)
    (hmem : CoprodI.of ⁅x, y⁆ ∈ letterRelatorSubgroup R) :
    ¬ RelativeLengthBound L R := by
  refine not_relativeLengthBound_of_short ?_ hmem ?_
  · intro h
    exact hxy (commutatorElement_eq_one_iff_mul_comm.mp
      (CoprodI.of_injective false (by rw [h, map_one])))
  · intro r hr
    have h1 := L.len_source_le_one ⁅x, y⁆
    have h2 := hfloor r hr
    omega

/-! ## 2.  An abelian partner kills every source commutator -/

/-- **A weighted router design with an abelian partner factor refutes its own
Greendlinger bound**, as soon as the source factor is nonabelian.

The tie makes the partner surject onto the routed quotient with no leaf spent,
so an abelian partner makes the quotient abelian and every source commutator
dies; the previous theorem then applies.  The source factor's nonabelianness is
stated at `G false` rather than at `U` so that no isomorphism has to be
transported. -/
theorem not_relativeLengthBound_of_abelian_partner {U H : Type} [Group U]
    [Group H] {G : Bool → Type} [∀ b, Group (G b)]
    (D : WeightedRouterDesign U H G) (hH : ∀ p q : H, p * q = q * p)
    {x y : G false} (hxy : x * y ≠ y * x) :
    ¬ RelativeLengthBound D.relLength D.relators := by
  refine not_relativeLengthBound_of_dead_commutator hxy
    (fun r hr => by have h := D.relators_long r hr; omega) ?_
  have hcomm : ∀ p q : D.Routed, p * q = q * p := by
    intro p q
    obtain ⟨a, rfl⟩ := D.partnerHom_surjective p
    obtain ⟨b, rfl⟩ := D.partnerHom_surjective q
    rw [← map_mul, ← map_mul, hH a b]
  have hcomm' : ∀ p q : D.Routed, p * q * p⁻¹ * q⁻¹ = 1 := by
    intro p q
    rw [hcomm p q]
    group
  have hker : QuotientGroup.mk' (letterRelatorSubgroup D.relators)
      (CoprodI.of ⁅x, y⁆) = 1 := by
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    exact hcomm' _ _
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hker
  exact hker

end RelHyp
end GGT
end GroupApproximation
