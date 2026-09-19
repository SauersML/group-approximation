import GroupApproximation.Higman.AmalgamPushout
import GroupApproximation.Higman.Pinch
import GroupApproximation.Sofic.ChiodoUniversalHost
import Mathlib.Computability.RE

/-!
# What Chiodo's Theorem 2.2 costs, itemized

`Sofic.ChiodoUniversalHost` reduces Chiodo's Theorem 3.10 --- the universal
finitely presented torsion-free group, which is Fournier-Facio's first input
and this repository's proof-ledger row `KC.21` --- to a single structure,
`ChiodoHost.TorsionFreeHigmanHull ChiodoAbsorber`: the assertion that one
explicitly constructed countable torsion-free group embeds in a finitely
presented torsion-free group.  Everything else about Theorem 3.10 is proved
there, unconditionally.

This file takes that one structure apart into the two theorems it actually
is, states both precisely in Lean, and proves that they compose.  It also
records what is now known about how each of the two would be proved, with the
part of the machinery that is already formalized named.

    Chiodo Theorem 2.2 at `ChiodoAbsorber`
        =  (A) Chiodo Theorem 2.2 in general  --- Higman embedding with the
                set of torsion orders preserved,
        +  (B) `ChiodoAbsorber` is recursively presented --- Chiodo
                Proposition 3.8, the effective torsion-free radical.

## (A), and how far the formalization of it has got

Input (A) is Higman's embedding theorem with Chiodo's torsion clause.  The
modern route, which is Higman's own rather than the Turing-machine route of
Rotman's Chapter 12, runs through *benign* subgroups, and the first section
of that theory is formalized in this repository:

* `Higman.Benign` --- the definition, and the two constructions that need
  only direct products: intersections (`BenignWitness.inf`) and kernels of
  maps to finitely presented groups (`BenignWitness.ker`).
* `Higman.BenignClosure` --- preimages (`BenignWitness.comap`), and finite
  intersections.
* `Higman.HNNCentralizer` --- the equation `G ∩ Gᵗ = G ∩ L` in the HNN
  extension whose stable letter centralizes `L` (`map_inf_conj_map`), proved
  from Mathlib's Britton lemma, together with the finite presentation of that
  extension.
* `Higman.AmalgamPresentation`, `Higman.AmalgamPushout` --- the amalgamated
  free product over a finitely generated subgroup is finitely presented, and
  is Mathlib's `PushoutI`, so its normal form theorem is available.
* `Higman.Pinch` --- the pinch lemma, proved: in `P ∗_M t`, if `Q ⊓ M ≤ Z`
  and `Z ⊓ M ≤ Q` then `⟨Z, Qᵗ⟩ ∩ P = Z`.
* `Higman.BenignJoin` --- **Higman's Lemma 3.2(2), proved**: benign subgroups
  are closed under joins (`Higman.Benign.sup`), by the direct-product gluing
  and two applications of the pinch lemma.  With `BenignWitness.inf` this
  completes Lemma 3.2, and with `BenignWitness.comap` half of Lemma 3.3.
* `Higman.PinchGraph`, `Higman.RopeTrick` --- **the rope trick, proved**:
  `Higman.fpOvergroup_of_benign` says that if `N` is benign in a finitely
  generated, finitely presented `F`, then `F ⧸ N` embeds in a finitely
  presented group.  This is the direction of Higman's Lemma that turns the
  benign theory into an embedding theorem; the easy direction is
  `BenignWitness.ker`.  The proof is the classical one: a second stable letter
  conjugating `S × 1` onto the graph of the map `τ : ⟨A, Aᵗ⟩ → F ⧸ N` which is
  the quotient map on `A` and trivial on `Aᵗ`, so that the relations of
  `F ⧸ N` become consequences of finitely many.  `τ` exists because `⟨A, Aᵗ⟩`
  is the amalgam of `A` and `Aᵗ` over `N`, and that is what the value-carrying
  descent of `Higman.PinchGraph` supplies.

The *join* half of Higman's Lemma 3.2 --- benign subgroups are closed under
joins --- comes down to one pinch lemma, `PinchProperty` below, and that
lemma is **proved**, in `Higman.Pinch`.  Two remarks about the route are
worth recording, because both are simplifications of the classical one:

* The literature glues the two witnesses with Mikaelian's `✻`-construction, a
  nested amalgam of HNN extensions.  It is not needed: gluing with the
  **direct product** `K₁ × K₂`, with `G` embedded diagonally, already makes
  `L₁ × ⊤` and `⊤ × L₂` finitely generated subgroups cutting out `A₁` and
  `A₂`, and the two stable letters can then be added over the same base.
  Finite presentation is then `ProductFinitePresentation.instProd` followed
  twice by `HNNFinitePresentation.isFinitelyPresented_hnnExtension`.
* With that gluing, the join follows from `PinchProperty` applied **twice**,
  and from nothing else: once inside `K ∗_{M₁} t₁` with `Z = ⟨A₁, A₂⟩` and
  `Q = G`, giving `⟨A₁, A₂, Gᵗ¹⟩ ∩ K = ⟨A₁, A₂⟩`; and once inside
  `(K ∗_{M₁} t₁) ∗_{M₂} t₂` with `Z = ⟨A₁, A₂, Gᵗ¹⟩` and `Q = G`, whose
  hypotheses are supplied by the first application.

What is left of (A) is stated as one structure, `Higman.REBenign` in
`Higman/EmbeddingTheorem.lean`: *a recursively enumerable normal subgroup of a
free group of finite rank is benign*.  That is Higman's Sections 2--4 --- the
sequence space, the operations `(H)`, and the closure of the benign family
under them --- and with it `Higman.fpOvergroup_of_fgRecursive` proves Higman's
embedding theorem for finitely generated groups outright, because the other
half is the rope trick, which is proved.  Of Section 3.2 the first example is
also proved (`Higman.Row.benign_row`: the row subgroup `⟨bᵢ : i ∈ ℤ⟩` of
`⟨b, c⟩` is benign).

Two further steps stood between that and input (A) as stated here.  Both have
since been reduced, and one of them removed:

* **from finitely generated to countably generated.**  Higman's theorem is
  about finitely generated groups; `ChiodoAbsorber` is countably generated.
  The bridge is the Higman--Neumann--Neumann embedding, and its group theory is
  now **proved** (`Higman.HNNEmb.nonempty_fgOvergroup`: every countable group
  embeds in a three-generator group), as is its torsion clause
  (`Higman.torsionFree_ext`, off this repository's own free-product and HNN
  permanence theorems).  What is left of it is the effectivity clause
  `Higman.BridgeRecursive`.
* **the torsion clause.**  Chiodo's Theorem 2.2 preserves the set of torsion
  orders.  This is now **proved to be no extra theorem about the rope trick**:
  `Higman.torsionFree_ropeGroup` shows the rope group is torsion-free as soon
  as the benign witness and the quotient are, so the clause is exactly the
  demand that the witness be torsion-free.  `Higman.REBenignTF` is that
  refinement of `REBenign`, and `Higman.torsionPreservation_of_reBenignTF`
  derives `TorsionPreservation` from it.

## (B)

Input (B) is that `ChiodoAbsorber` is recursively presented.  It splits again:

* (B1) the *direct sum* `Monsters.CodedDirectSum` is recursively presented.
  This one is within the repository's existing computability layer: a word is
  trivial in a restricted direct product exactly when each of its finitely
  many coordinates is trivial, and the word problem of a finitely presented
  group is recursively enumerable, which is
  `Computability.WordProblemRE.rePred_wordProblemPred`.
* (B2) the universal torsion-free quotient of a recursively presented group
  is recursively presented.  This is Chiodo's Proposition 3.8, and its proof
  is his Lemmas 3.5--3.7: the set of words representing torsion elements
  modulo a recursively enumerable set is again recursively enumerable,
  uniformly in the stage of the tower `Algebra.TorsionFreeRadicalTower`
  formalizes.

Neither is proved here.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Monsters
open GroupApproximation.ChiodoHost

/-! ## 1.  The pinch lemma the join needs -/

/-- **The pinch lemma.**  In the HNN extension whose stable letter
centralizes `M`, let `Z` and `Q` be subgroups of the base which *cover each
other's intersection with* `M`.  Then the subgroup generated by `Z` and by
the conjugate `Qᵗ` meets the base in `Z` exactly.

This is the one statement the join of benign subgroups needs, and it is the
only place where a word argument is required: an element of `⟨Z, Qᵗ⟩` is a
product

    z₀ · t⁻¹q₁t · z₁ · t⁻¹q₂t ⋯ zₖ,

which is a *reduced* word in the sense of Mathlib's
`HNNExtension.ReducedWord` unless some `qᵢ ∈ M` or some interior `zᵢ ∈ M`.
The two hypotheses are exactly what lets those two cases be absorbed --- a
`qᵢ ∈ Q ⊓ M` lands in `Z` and merges with its neighbours, an interior
`zᵢ ∈ Z ⊓ M` lands in `Q` and merges with its neighbours --- so the length
drops, and the induction ends at a reduced word, where Britton's lemma
forbids the product from lying in the base at all.

`Higman.HNNCentralizer.mem_of_conj_mem_range` is the one-letter case, and
`Higman.Pinch.pinch` is the general case; `pinchProperty` below is the
statement in the packaged form, discharged. -/
def PinchProperty : Prop :=
  ∀ (P : Type) [Group P] (M Z Q : Subgroup P),
    Q ⊓ M ≤ Z → Z ⊓ M ≤ Q →
      Subgroup.closure
          (((Z.map (HNNExtension.of : P →* CentHNN M)) : Set (CentHNN M)) ∪
            ((Q.map (HNNExtension.of : P →* CentHNN M)).map
              (conjT M).toMonoidHom : Set (CentHNN M)))
        ⊓ (HNNExtension.of : P →* CentHNN M).range
      ≤ (Z.map (HNNExtension.of : P →* CentHNN M))

/-- **The pinch lemma holds.**  `Higman.Pinch.pinch` proves it: the block-word
induction of that file, with Britton's lemma at the base. -/
theorem pinchProperty : PinchProperty := by
  intro P _ M Z Q hQZ hZQ
  exact Pinch.pinch M Z Q hQZ hZQ

/-! ## 2.  Recursive presentations -/

/-- Raw words in countably many generators: a letter is an index together
with a sign.  This is the alphabet the repository's computability layer
already uses (`Computability.RawWord`), so that "recursively enumerable set
of words" is a statement about a `Primcodable` type. -/
abbrev RawWord : Type := List (ℕ × Bool)

/-- The value of a raw word under an assignment of generators. -/
def evalRaw {A : Type} [Group A] (x : ℕ → A) : RawWord → A
  | [] => 1
  | (i, b) :: w => (if b then x i else (x i)⁻¹) * evalRaw x w

@[simp] theorem evalRaw_nil {A : Type} [Group A] (x : ℕ → A) :
    evalRaw x ([] : RawWord) = 1 := rfl

@[simp] theorem evalRaw_cons {A : Type} [Group A] (x : ℕ → A) (i : ℕ) (b : Bool)
    (w : RawWord) :
    evalRaw x ((i, b) :: w) = (if b then x i else (x i)⁻¹) * evalRaw x w := rfl

/-- **A countably generated recursive presentation**, in the form Chiodo's
Theorem 2.2 consumes: a countable generating family together with the
statement that the set of words representing the identity is recursively
enumerable.

This is equivalent to the textbook form --- a presentation `⟨X | R⟩` with `R`
recursively enumerable --- because the consequences of a recursively
enumerable set of relators are recursively enumerable, and conversely a group
is presented by the whole of its word problem. -/
structure RecursivePresentation (A : Type) [Group A] where
  /-- The generators. -/
  gen : ℕ → A
  /-- They generate. -/
  spans : Subgroup.closure (Set.range gen) = ⊤
  /-- The word problem is recursively enumerable. -/
  re : REPred (fun w : RawWord => evalRaw gen w = 1)

/-! ## 3.  The two inputs, and their composite -/

/-- **Input (A): Chiodo, arXiv:1107.1489v4, Theorem 2.2.**  A countably
generated recursive presentation of a torsion-free group embeds in a finitely
presented torsion-free group.

The torsion-freeness of the output is Chiodo's torsion-order clause,
specialized by `ChiodoHost.torsionOrders_eq_empty_iff`, which is proved.

**Nothing inhabits this structure.**  Its content is Higman's embedding
theorem; §1 of the docstring above says which parts of the standard proof are
already formalized in this repository and which are not. -/
structure TorsionFreeHigmanEmbedding where
  /-- The embedding theorem, at every recursively presented torsion-free
  group. -/
  hull : ∀ (A : Type) [Group A], RecursivePresentation A → IsPowerTorsionFree A →
    Nonempty (TorsionFreeHigmanHull A)

/-- **Input (B): Chiodo, arXiv:1107.1489v4, Proposition 3.8, at the
absorber.**  The group `Monsters.ChiodoAbsorber` is recursively presented.

**Nothing inhabits this structure.**  §2 of the docstring above splits it
into the syntactic half (B1), which the repository's computability layer can
reach, and the effective-radical half (B2), which is Chiodo's Proposition
3.8 proper. -/
structure AbsorberRecursivePresentation where
  /-- The recursive presentation. -/
  presentation : RecursivePresentation ChiodoAbsorber

/-- **The two inputs compose to the one this replaces.**

Given Chiodo's Theorem 2.2 and a recursive presentation of the absorber, the
hull exists --- and with it, through
`ChiodoHost.universalTorsionFreeHost`, Chiodo's Theorem 3.10 and the first
input of `KC.21`.

The torsion-freeness the embedding theorem asks for is supplied by
`Monsters.chiodoAbsorber_torsionFree`, which is proved unconditionally. -/
theorem nonempty_hull_of_inputs (hA : TorsionFreeHigmanEmbedding)
    (hB : AbsorberRecursivePresentation) :
    Nonempty (TorsionFreeHigmanHull ChiodoAbsorber) :=
  hA.hull ChiodoAbsorber hB.presentation chiodoAbsorber_torsionFree

/-- The same, landing on the universal group itself: the two inputs give
Chiodo Theorem 3.10, hence `FournierFacioUniversal.UniversalTorsionFreeHost`,
hence `KC.21`'s first input. -/
theorem nonempty_universalTorsionFreeHost_of_inputs
    (hA : TorsionFreeHigmanEmbedding) (hB : AbsorberRecursivePresentation) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost := by
  obtain ⟨H⟩ := nonempty_hull_of_inputs hA hB
  exact ⟨universalTorsionFreeHost H⟩

end Higman
end GroupApproximation
