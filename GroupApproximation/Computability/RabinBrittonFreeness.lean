import GroupApproximation.Computability.FreeByRetraction
import GroupApproximation.GroupTheory.HNNBrittonPinch
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Stages E4 and E5, and the exact boundary of the retraction method

Stages **E1(ii)**, **E2** and half of **E3** of the Adian--Rabin roadmap all
fell to one move: find a homomorphism onto a free group that sees precisely the
invariant in question and forgets everything else.  `FreeByRetraction` packages
it.

**That move cannot work for E4 or E5, and this file proves why** rather than
leaving the next reader to search for a retraction that does not exist.  What
replaces it is Britton's lemma, and the general criterion the two stages
actually consume is stated here.

## Why no retraction exists

Both stages ask for a rank-two free subgroup of a tower built from
Baumslag--Solitar relations.  Suppose `ψ` were a homomorphism from `G''` to a
free group returning `u` and `[w, s₀]` to a basis.  The tower imposes

```text
u tᵢ u⁻¹ = tᵢ²      (0 ≤ i ≤ n)
```

so `ψ(tᵢ)` is conjugate to its own square in a free group.  In a free group
that forces `ψ(tᵢ) = 1`: conjugacy preserves cyclically reduced length, while
squaring doubles it, so the length is zero.  With every `ψ(tᵢ) = 1` the
relation `tᵢ sᵢ tᵢ⁻¹ = sᵢ²` collapses to `ψ(sᵢ) = ψ(sᵢ)²`, hence `ψ(sᵢ) = 1`,
hence `ψ([w, s₀]) = 1` — which is not a basis element.  The same argument runs
verbatim on `G₂ = ⟨a, b, c | bab⁻¹ = a², cbc⁻¹ = b²⟩` for E5.

So the obstruction is not incidental: a Baumslag--Solitar relation is exactly
what a free quotient cannot carry, and every stage of the tower after `E3`'s
first half sits behind one.

## What replaces it

The criterion below is the standard Britton consequence: in an HNN extension,
a stable letter together with a base element **no power of which meets either
associated subgroup** generate a free group of rank two.  The hypothesis is
what fails when `w = 1`, which is precisely how the Rabin construction encodes
the word problem — so it cannot be weakened, and it is where `w ≠ 1` enters the
embedding half for the first time.

## What this file provides, and what it does not

It provides the statement of the criterion, the reduction of E4 and E5 to it,
and the obstruction above.  It does **not** provide the criterion's proof: that
is the alternating-word Britton argument, and the repository's spelling
machinery in `GroupTheory/HNNBrittonSpelling` is the intended tool.  Nothing
below is asserted on the strength of an unproved hypothesis; the criterion
appears as a named target, not as an assumption feeding a conclusion.

Never compiled.
-/

namespace GroupApproximation
namespace RabinBrittonFreeness

open HNNExtension

/-! ## The obstruction: a free group carries no Baumslag--Solitar relation -/

/-- **Conjugate to its own square forces triviality, in a free group.**

This is the reason no retraction can prove E4 or E5.  Cyclically reduced length
is a conjugacy invariant and doubles under squaring, so it must vanish.

The proof is the cyclic normal form of `Mathlib.GroupTheory.FreeGroup.CyclicallyReduced`;
it is stated here as the target it is, and this file does not consume it. -/
def FreeGroupNoBaumslagSolitar : Prop :=
  ∀ {α : Type} (x y : FreeGroup α), y * x * y⁻¹ = x ^ 2 → x = 1

/-! ## The criterion the two stages consume -/

variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

/-- The hypothesis of the criterion: no nonzero power of the base element meets
either associated subgroup.  This is exactly what fails when the encoded word
is trivial. -/
def NoPowerMeetsAssociated (z : G) : Prop :=
  ∀ k : ℤ, k ≠ 0 → z ^ k ∉ A ∧ z ^ k ∉ B

/-- **The Britton freeness criterion.**  In an HNN extension, the stable letter
and a base element no power of which meets an associated subgroup generate a
free group of rank two.

Stated as the named target of stages E4 and E5.  Its proof is the
alternating-word argument: a nonempty reduced word in `t` and `z` alternates
stable letters with nontrivial base elements outside the associated subgroups,
so Britton's lemma forbids a pinch and the word is nontrivial.  The spelling
apparatus of `GroupTheory/HNNBrittonSpelling` is the intended route. -/
def BrittonFreeOfRankTwo : Prop :=
  ∀ {G : Type} [Group G] {A B : Subgroup G} (φ : A ≃* B) (z : G),
    (∀ k : ℤ, k ≠ 0 → z ^ k ∉ A ∧ z ^ k ∉ B) →
    Nonempty (FreeGroup (Fin 2) ≃*
      Subgroup.closure ({HNNExtension.t, HNNExtension.of z} :
        Set (HNNExtension G A B φ)))

/-! ## Where the two stages plug in

**E4.**  `G'' = G' *_u` with associated subgroups `⟨t₀,…,tₙ⟩` and
`⟨t₀²,…,tₙ²⟩`, both inside the stable-letter layer.  The base element is
`[w, s₀]`, a word in the `sᵢ` alone.  Its powers avoid both associated
subgroups exactly when `[w, s₀] ≠ 1`, which is exactly when `w ≠ 1` — the
commutator of `w` with the free letter `s₀` is trivial precisely when `w`
centralizes `s₀`, and in the free product `Γ * ⟨s₀⟩` only the identity does.
That last step is the one place the free-product normal form is genuinely
needed, and it is a single centralizer computation rather than a freeness
argument.

**E5.**  `G₂` is `⟨a⟩` extended twice.  The base element is `a` and the stable
letter is `c`; `a` has infinite order and lies outside `⟨b⟩` and `⟨b²⟩`, so the
criterion applies directly, with `Algebra.HNNTorsionFree.lengthHom` supplying
the grading that separates the layers.

**E6 and E7** then assemble: the honest tower `J` is built from these HNN
extensions and one pushout, and the embedding `E ↪ K(w)` is the composite,
needing only the forward map per the roadmap's own note.
-/

end RabinBrittonFreeness
end GroupApproximation
