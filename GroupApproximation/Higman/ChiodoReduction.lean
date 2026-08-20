import GroupApproximation.Higman.EmbeddingTheorem

/-!
# From Higman's theorem to Chiodo's Theorem 2.2

`Higman.EmbeddingTheorem` proves Higman's embedding theorem for finitely
generated groups from one input, `REBenign`.  Chiodo's Theorem 2.2 --- input
(A) of `Higman.Program`, and the last thing between this repository and
Chiodo Theorem 3.10 --- asks for two things Higman's theorem does not give:

* it is stated for *countably generated* recursive presentations, and
  `Monsters.ChiodoAbsorber` is countably generated, not finitely generated;
* it preserves the set of torsion orders, so a torsion-free input gives a
  torsion-free output.

This file names those two gaps, states them as the two structures they are,
and proves that together they give input (A).  Nothing here is a new
mathematical claim: it is the bookkeeping that says exactly what is missing
and that nothing else is.

## The two inputs

* `CountableToFG` --- the Higman--Neumann--Neumann bridge, with the clauses
  the application needs: a countably generated recursively presented
  torsion-free group embeds in a *finitely generated* one that is still
  recursively presented and still torsion-free.  The classical construction is
  the HNN extension of `A ∗ F₂` identifying `xⁱ y x⁻ⁱ` with `gᵢ xⁱ y x⁻ⁱ`
  along an enumeration `gᵢ` of `A`; the clauses then need the free product of
  torsion-free groups to be torsion-free (Kurosh) and the HNN extension to
  preserve torsion-freeness, neither of which is in Mathlib.
* `TorsionPreservation` --- Higman's theorem with Chiodo's torsion clause, at
  finitely generated groups.  The rope trick's output is an HNN extension of
  `Γ × (F ⧸ N)` over subgroups of `Γ × 1`, and `Γ` is an HNN extension of the
  benign witness, so the clause reduces to the two standard facts that torsion
  in an HNN extension is conjugate into the base and torsion in a direct
  product is coordinatewise --- again the first is not in Mathlib.

Neither structure is inhabited here.

## How `TorsionPreservation` relates to `REBenign`

`TorsionPreservation` is the torsion-strengthened form of what `REBenign`
already gives: `Higman.fpOvergroup_of_fgRecursive` proves the same statement
without the torsion clause.  It is kept as a separate input rather than
derived, because the derivation needs more than a torsion argument bolted on
at the end.  The rope group is built over the benign witness `K`, which
`REBenign` supplies with no control on its torsion at all, so a torsion-free
output needs `REBenign` to produce *torsion-free witnesses* --- which is
exactly the refinement Chiodo's Theorem 2.2 states as `Tord(P⁻) = Tord(T(P))`,
and is why he states it that way rather than citing Higman.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.ChiodoHost

/-- A finitely generated recursive, torsion-free hull of a countable group. -/
structure FGHull (A : Type) [Group A] where
  /-- The finitely generated overgroup. -/
  Carrier : Type
  /-- Its group structure. -/
  [group : Group Carrier]
  /-- It is finitely generated and recursively presented. -/
  recursive : FGRecursive Carrier
  /-- It is still torsion-free. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- The embedding. -/
  emb : A →* Carrier
  /-- ... which is one. -/
  emb_injective : Function.Injective emb

attribute [instance] FGHull.group

/-- **Input: the Higman--Neumann--Neumann bridge with its two clauses.**

**Nothing inhabits this structure.** -/
structure CountableToFG where
  /-- Countably generated, recursively presented and torsion-free implies
  embeddable in a finitely generated group with the same two properties. -/
  bridge : ∀ (A : Type) [Group A], RecursivePresentation A →
    IsPowerTorsionFree A → Nonempty (FGHull A)

/-- **Input: Higman's theorem with Chiodo's torsion clause.**

**Nothing inhabits this structure.**  `Higman.fpOvergroup_of_fgRecursive`
proves the same statement without the torsion clause, from `REBenign`. -/
structure TorsionPreservation where
  /-- A finitely generated recursively presented torsion-free group embeds in a
  finitely presented *torsion-free* group. -/
  hull : ∀ (B : Type) [Group B], FGRecursive B → IsPowerTorsionFree B →
    Nonempty (TorsionFreeHigmanHull B)

/-- Composing an embedding with a hull. -/
def TorsionFreeHigmanHull.comp {A B : Type} [Group A] [Group B]
    (H : TorsionFreeHigmanHull B) (f : A →* B) (hf : Function.Injective f) :
    TorsionFreeHigmanHull A where
  Carrier := H.Carrier
  torsionFree := H.torsionFree
  emb := H.emb.comp f
  emb_injective := H.emb_injective.comp hf

/-- **The two inputs give Chiodo's Theorem 2.2.**  Bridge to a finitely
generated group, apply Higman with the torsion clause there, and compose the
two embeddings. -/
def torsionFreeHigmanEmbedding_of_inputs (hb : CountableToFG)
    (ht : TorsionPreservation) : TorsionFreeHigmanEmbedding where
  hull := by
    intro A _ p htf
    obtain ⟨u⟩ := hb.bridge A p htf
    obtain ⟨H⟩ := ht.hull u.Carrier u.recursive u.torsionFree
    exact ⟨H.comp u.emb u.emb_injective⟩

/-- **The whole chain, in one statement.**  The bridge, the torsion clause and
a recursive presentation of the absorber give Chiodo's Theorem 3.10, hence
`KC.21`'s first input.

Every other step --- the torsion-free radical and its universal quotient, the
absorber and its absorbing property, Definition 2.1 and the torsion-order
clause, Higman's Lemma 3.2 and Lemma 3.3, the pinch lemma, the rope trick, and
the assembly of Higman's embedding theorem from `REBenign` --- is proved in
this repository. -/
theorem nonempty_universalTorsionFreeHost_of_three (hb : CountableToFG)
    (ht : TorsionPreservation) (hB : AbsorberRecursivePresentation) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost :=
  nonempty_universalTorsionFreeHost_of_inputs
    (torsionFreeHigmanEmbedding_of_inputs hb ht) hB

end Higman
end GroupApproximation
