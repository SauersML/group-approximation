import GroupApproximation.Algebra.RabinVariantTower
import Mathlib.GroupTheory.PresentedGroup

/-!
# The presentation of the variant construction

`Algebra.RabinVariantTower` builds the tower and proves both halves of the
biconditional for it.  The Adian--Rabin reduction, however, is a statement about
a *presentation*: the map it needs is `w ↦ P(w)` with `P(w)` a finite
presentation.  This file writes that presentation down and maps it into the
tower.

The generators are the source generators `xᵢ`, the free letter `s`, one letter
`tᵢ` for each `sᵢ`, and the four cascade letters `u`, `b`, `c`, `k`.  The
relators are the source relators together with

    `u tᵢ u⁻¹ (tᵢ sᵢ)⁻¹`,   `b u b⁻¹ u⁻²`,   `c b c⁻¹ b⁻²`,   `k z k⁻¹ c⁻¹`,

where `sᵢ` is `s` for `i = 0` and `s xᵢ₋₁` otherwise, and `z = ⁅w, s⁆`.

`toTower` is the homomorphism into the tower, and it exists because every one of
those relators holds there --- which is exactly what
`RabinVariantTower.conj_t_eq_ts`, `casc1_conj`, `casc2_conj` and `full_conj`
say.  Composing with it turns the tower's `full_base_injective` into the
statement the reduction needs: the source group embeds in the *presented*
group.
-/

namespace GroupApproximation
namespace RabinVariantPresentation

open RabinVariantTower

/-- The letters adjoined to the source generators. -/
inductive Extra (m : ℕ) : Type
  | s : Extra m
  | t : Fin (m + 1) → Extra m
  | u : Extra m
  | b : Extra m
  | c : Extra m
  | k : Extra m
  deriving DecidableEq

/-- The generators of the presentation. -/
abbrev Gen (m : ℕ) : Type := Fin m ⊕ Extra m

variable {m : ℕ}

/-- A source generator, as a word. -/
def X (i : Fin m) : FreeGroup (Gen m) := FreeGroup.of (Sum.inl i)

/-- The free letter, as a word. -/
def S : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.s)

/-- The `i`th stable letter of the killing layer, as a word. -/
def T (i : Fin (m + 1)) : FreeGroup (Gen m) := FreeGroup.of (Sum.inr (Extra.t i))

/-- The cascade letters, as words. -/
def U : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.u)
/-- The second cascade letter. -/
def B : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.b)
/-- The third cascade letter. -/
def C : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.c)
/-- The last cascade letter. -/
def K : FreeGroup (Gen m) := FreeGroup.of (Sum.inr Extra.k)

/-- `sᵢ`: the letter `s` at `i = 0`, and `s xᵢ₋₁` afterwards.  The change of
generators, at the level of words. -/
def sWord (i : Fin (m + 1)) : FreeGroup (Gen m) :=
  if h : (i : ℕ) = 0 then S
  else S * X ⟨(i : ℕ) - 1, by omega⟩

/-- The source generators, embedded in the larger free group. -/
def emb : FreeGroup (Fin m) →* FreeGroup (Gen m) := FreeGroup.map Sum.inl

/-- The witness word `z = ⁅w, s⁆`. -/
def Z (w : FreeGroup (Fin m)) : FreeGroup (Gen m) :=
  emb w * S * (emb w)⁻¹ * S⁻¹

/-- **The relators.**  The source relators, the killing relations, and the
cascade. -/
def relators (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) :
    Set (FreeGroup (Gen m)) :=
  (fun r => emb r) '' R
    ∪ Set.range (fun i : Fin (m + 1) => U * T i * U⁻¹ * (T i * sWord i)⁻¹)
    ∪ {B * U * B⁻¹ * (U ^ 2)⁻¹, C * B * C⁻¹ * (B ^ 2)⁻¹,
        K * Z w * K⁻¹ * C⁻¹}

/-- **The presented group of the construction.** -/
abbrev Pres (R : Set (FreeGroup (Fin m))) (w : FreeGroup (Fin m)) : Type :=
  PresentedGroup (relators R w)

/-! ## Mapping the presentation into the tower

Every relator holds in the tower, so the presentation maps into it.  The four
families of relators are discharged by the four conjugation lemmas of
`RabinVariantTower`, and the source relators by the fact that the source group
sits inside. -/

variable {Γ : Type} [Group Γ] (x : Fin (m + 1) → Γ)

/-- Where the generators go in the tower.  The source generators go to the
image of `Γ`; the extra letters go to the letters of the tower. -/
noncomputable def towerGen {z : Casc2 x} (hz : ∀ n : ℤ, n ≠ 0 → z ^ n ≠ 1)
    (xs : Fin m → Γ) : Gen m → Full x hz
  | Sum.inl i => HNNExtension.of (casc2OfBase x (xs i))
  | Sum.inr Extra.s =>
      HNNExtension.of (casc2OfMid x (midOfBase (RabinVariantTower.s)))
  | Sum.inr (Extra.t i) => HNNExtension.of (casc2OfMid x (RabinVariantTower.t i))
  | Sum.inr Extra.u =>
      HNNExtension.of (HNNExtension.of (HNNExtension.of HNNExtension.t))
  | Sum.inr Extra.b => HNNExtension.of (HNNExtension.of HNNExtension.t)
  | Sum.inr Extra.c => HNNExtension.of HNNExtension.t
  | Sum.inr Extra.k => HNNExtension.t

/-! ## What blocks the next step, measured

The remaining work is to check that each relator dies in the tower, which turns
`towerGen` into a homomorphism `Pres R w →* Full x hz` and, composed with
`RabinVariantTower.full_base_injective`, gives the source group embedded in the
*presented* group.

Every one of those checks is a one-line consequence of a conjugation lemma
already proved --- `conj_t_eq_ts`, `casc1_conj`, `casc2_conj`, `full_conj` ---
pushed up the cascade by `congrArg` and `map_mul`.  They do not typecheck yet,
and the reason is not mathematical:

  `Casc1`, `Casc2` and `Full` are `abbrev`s, hence reducible, so every
  elaboration inside them unfolds four nested `HNNExtension`s together with the
  `cycEquiv` and injectivity proofs embedded in their types.  The result is
  exponential in the number of layers.  `congrArg` across three layers times out
  at `isDefEq`, and it still times out at a heartbeat limit of 1000000, so this
  is term size and not a budget that wants raising.

The fix is the one `Computability.BooneGroupTower` already uses for the same
reason: make each layer an opaque `def` carrying its own `Group` instance, and
expose its stable letter as a named definition rather than as
`HNNExtension.t` at a reducible type.  The layers then never unfold, and the
conjugation lemmas transport across them as ordinary homomorphism applications.

That refactor is not done here.  What is here --- the presentation, its
relators, and where each generator goes in the tower --- is independent of it,
and the four conjugation lemmas it needs are already proved in
`Algebra.RabinVariantTower`. -/

end RabinVariantPresentation
end GroupApproximation
