import GroupApproximation.Monsters.P13DescentMaster

/-!
# `SL₃(ℤ)` is finitely presented

The workstream that produced this file was dispatched to *scaffold* the
Steinberg route to a finite presentation of `SL₃(ℤ)`: build `St₃(ℤ)` on six
generators, evaluate it onto the matrix group, exhibit the central symbol
`{-1,-1}`, and leave the unstable computation `K₂(3,ℤ) = ⟨{-1,-1}⟩` as a
sorried atom.  That scaffold is unnecessary.  **The route is already walked,
end to end and with complete proofs, inside this repository**, and this module does
nothing but name the endpoint and record where it comes from.

## Why the atom is not open

`Sofic/LiteralP13Presentation.lean` defines `P13` as a `PresentedGroup` on six
generators `e₁₂,e₁₃,e₂₁,e₂₃,e₃₁,e₃₂` and thirteen relators, and the split of
those thirteen is exactly the split the Steinberg route asks for:

* relators `0,…,5` are the ordered Steinberg conjugation relations
  `xᵢⱼ xⱼₖ xᵢⱼ⁻¹ = xᵢₖ xⱼₖ` for the six ordered triples;
* relators `6,…,11` are the six commuting-root commutators;
* relator `12` is `(e₁₂ e₂₁⁻¹ e₁₂)⁴`, and that word **is** the Steinberg symbol
  `{-1,-1} = h₁₂(-1)²`.

So `P13` is the finitely presented group `St₃(ℤ)/⟪{-1,-1}⟫` on the nose, and
the Steinberg route's remaining step — that this quotient *is* `SL₃(ℤ)` — is
`P13DescentMaster.p13CompletenessEquiv`, proved by the descent programme of
`Monsters/P13*.lean`, axiom-clean and with no incomplete proofs anywhere in
its import closure.  Surjectivity is Euclidean reduction
(`SL3ElementaryGeneration.toSL3_surjective`); injectivity is the descent normal
form (`P13DescentMaster.toSL3_injective`).

## What is proved here, and what is not

Proved: `SL₃(ℤ)` is finitely presented, on the displayed six generators and
thirteen relators.

*Not* proved, here or anywhere in this repository, and not needed by anything
downstream: that `K₂(3,ℤ) ≅ ℤ/2`.  That statement is about the *unstable
Steinberg group* `St₃(ℤ)` and asserts in addition that `{-1,-1} ≠ 1` there.
Completeness of a presentation is a statement about the quotient and says
nothing about whether the killed element was already trivial.  Reading
`p13CompletenessEquiv` as "`K₂(3,ℤ) = ℤ/2`" would be a strictly stronger claim
than the theorem supports; the honest reading is the one in
`isFinitelyPresented_SL3` below.
-/

namespace GroupApproximation
namespace SteinbergSL3

open LiteralP13Presentation LiteralP13MatrixModel

noncomputable section

/-! ## The Steinberg symbol -/

/-- The Weyl word `w₁₂ = w₁₂(1)⁻¹ = e₁₂ e₂₁⁻¹ e₁₂`.

With `wᵢⱼ(a) = xᵢⱼ(a) xⱼᵢ(-a⁻¹) xᵢⱼ(a)` the two unit parameters coincide:
`w₁₂(-1) = e₁₂⁻¹ e₂₁ e₁₂⁻¹ = w₁₂(1)⁻¹`, so `h₁₂(-1) = w₁₂(-1) w₁₂(1)⁻¹` is the
square of this word and the symbol `{-1,-1} = h₁₂(-1)²` is its fourth power. -/
def weylWord : P13 := E12 * E21⁻¹ * E12

/-- The Steinberg symbol `{-1,-1} = h₁₂(-1)²`, as a word in the six generators.

`h₁₂(-1) = weylWord²`, so the symbol is `weylWord⁴`, which is literally relator
`12` of the presentation. -/
def steinbergSymbol : P13 := weylWord ^ 4

/-- **The symbol is killed by the presentation.**  This is relator `12`, so the
proof is a lookup rather than a computation: `P13` is `St₃(ℤ)` modulo exactly
this element. -/
theorem steinbergSymbol_eq_one : steinbergSymbol = 1 := by
  have h := P13SteinbergCalculus.weyl_fourth_power
  simp only [steinbergSymbol, weylWord, pow_succ, pow_zero, one_mul]
  exact h

/-! ## Completeness, restated -/

/-- **The presentation is complete**: the thirteen relators generate every
relation among the six elementary matrices.  This is
`P13DescentMaster.toSL3_injective` in kernel form, and it is the statement that
replaces the sorried `K₂` atom. -/
theorem ker_toSL3_eq_bot : (toSL3).ker = ⊥ :=
  MonoidHom.ker_eq_bot toSL3 P13DescentMaster.toSL3_injective

/-- **`SL₃(ℤ)` is finitely presented.**

Six generators, thirteen relators.  Every input is proved in this repository:
finite presentation of `P13` is the `PresentedGroup` instance on a finite
generator type with a finite relator set, and `p13CompletenessEquiv` is the
completeness theorem. -/
instance isFinitelyPresented_SL3 : Group.IsFinitelyPresented SL3 :=
  Group.IsFinitelyPresented.equiv P13DescentMaster.p13CompletenessEquiv

/-- `isFinitelyPresented_SL3` at the unabbreviated spelling, so that a search
for the matrix group finds it. -/
theorem isFinitelyPresented_specialLinearGroup :
    Group.IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin 3) ℤ) :=
  isFinitelyPresented_SL3

end

end SteinbergSL3
end GroupApproximation
