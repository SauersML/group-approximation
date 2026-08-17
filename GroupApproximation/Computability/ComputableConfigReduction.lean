import GroupApproximation.Computability.ModularMachineUndecidable
import GroupApproximation.Computability.MarkovReductionInterface

/-!
# From an indexed halting problem to the halting problem on configurations

`ModularMachineUndecidable.exists_modularMachine_halting_not_computablePred`
produces a modular machine `mm` together with a map `f : ℕ → ℕ × ℕ` along which
halting is undecidable.  What the Adian--Rabin lane needs instead is the
undecidability of

    fun p : ℕ × ℕ => mm.Halts p

on the machine's *own* configurations, with no indexing map anywhere: the words
attached to a configuration `(i, j)` in `G_M` are explicit in `i` and `j`, so a
statement in that form keeps every encoding difficulty on the machine side and
lets the group side stay arithmetic.  See `D4'` in the debt table of
`Computability.AdianRabinMarkovProperty`.

## The gap, and why it is not a formality

`¬ComputablePred (fun m => mm.Halts (f m))` does **not** give
`¬ComputablePred mm.Halts`.  Composing a computable predicate with an arbitrary
`f` need not be computable, so the hypothesis is consistent with `mm.Halts`
being decidable and `f` being wild.  The implication runs the other way and
needs `f` computable, which is exactly what this file isolates.

## What is proved here

* `not_computablePred_of_computable_reduction` --- the contrapositive of
  pullback along a computable function, in the shape a many-one reduction is
  actually used in.  The pullback itself is
  `MarkovMFConsequences.computablePred_comp`, which is already general in both
  types; note that `Computability.computablePred_comp` in `UniversalCodeHalting`
  is a *different* lemma specialised to `p : ℕ → Prop` and does not apply here,
  since the configurations live in `ℕ × ℕ`.
* `exists_modularMachine_config_halting_not_computablePred_of_computable` ---
  the target, **conditional on the index map being computable**.

## What remains

Exactly the hypothesis of the last theorem: that the map

    f m = (D.toQuad M₁).encCfg (D.initQCfg (TM2to1.trInit K'.main (trList [m])))

built inside `exists_modularMachine_halting_not_computablePred` is computable.
That map is more tractable than it looks and does *not* require carrying
`Primrec` through `PartrecToTM2 → TM2to1 → TM1to0`.  Unfolding the definitions
in that proof:

* `initQCfg l = ⟨[], l.map encodeSym, stIdx default false true, true⟩`, so the
  back stack is empty and the side is fixed;
* `encCfg` on such a configuration is
  `(tagA (stIdx default false true), encList base (l.map encodeSym))`, since
  `encList _ [] = 0` --- so the **first component is a constant**;
* `trList [m] = trNat m ++ [Γ'.cons]` and `trInit` reverses, tags the head and
  leaves the tail, so the symbol list is `Γ'.cons` followed by the reversed
  binary digits of `m`;
* `Γ'` has four constructors and each occurs in two flavours (head-tagged and
  not), so `encodeSym` contributes at most **eight fixed naturals**.

Hence `f m = (A, C + base * E m)` where `E 0 = 0` and
`E m = (if m even then a else b) + base * E (m / 2)`.  The choice-based
`Fintype.equivFin` inside `TMData.ofFintype` never has to be *evaluated*: it
only has to be constant, and a function assembled from finitely many constants
and arithmetic is computable regardless of whether those constants can be
computed.  This is the same observation that makes the code in `D4'` harmless
while the *words* are the real obligation.
-/

namespace GroupApproximation
namespace Computability

open Turing

/-- **A many-one reduction transfers undecidability**, provided the reduction is
computable.  This is the direction the halting arguments use, and the
computability hypothesis is not removable: without it the composite can fail to
be computable while the predicate itself is decidable. -/
theorem not_computablePred_of_computable_reduction {α β : Type} [Primcodable α]
    [Primcodable β] {p : β → Prop} {f : α → β} (hf : Computable f)
    (h : ¬ ComputablePred fun a => p (f a)) : ¬ ComputablePred p :=
  fun hp => h (MarkovMFConsequences.computablePred_comp hp hf)

/-- **The halting problem of a fixed modular machine, on its own
configurations**, granted a computable index map.

The hypothesis is the whole of the remaining obligation: it asks for the *same*
machine to carry both an undecidable indexed halting problem and a computable
index map.  Threading one `mm` through both is deliberate --- two separate
existentials could choose different machines, and the group side attaches its
words to the configurations of one particular machine. -/
theorem exists_modularMachine_config_halting_not_computablePred_of_computable
    (h : ∃ (mm : BooneGroup.ModularMachine) (f : ℕ → ℕ × ℕ), Computable f ∧
      ¬ ComputablePred fun m : ℕ => mm.Halts (f m)) :
    ∃ mm : BooneGroup.ModularMachine,
      ¬ ComputablePred fun p : ℕ × ℕ => mm.Halts p := by
  obtain ⟨mm, f, hf, hnc⟩ := h
  exact ⟨mm, not_computablePred_of_computable_reduction hf hnc⟩

end Computability
end GroupApproximation
