import Mathlib.Computability.TuringMachine.ToPartrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.Halting

/-!
# A fixed universal code, and the machine that runs it

Steps **U1** and **U2** of the universal-machine debt recorded in
`Computability.SemigroupWordProblem`.  That module proves the reduction half of
Markov--Post in full; what it lacks -- and what step **D3** of the ledger in
`Computability.AdianRabinMarkovProperty` lacks, and what Simpson's Theorem 4
lacks on the modular-machine route to Novikov--Boone -- is a *single* machine
whose halting problem is undecidable.  Undecidability of any property of a
machine model forces that model to be universal, so this cannot be routed
around; it has to be built once.

Mathlib supplies every mathematical ingredient, and none of them is reproved
here.  What was missing was the plumbing between three different presentations
of "partial recursive":

* `Nat.Partrec.Code.eval : Code → ℕ →. ℕ` with `eval_part : Partrec₂ eval`, the
  universal partial function;
* `Nat.Partrec'`, an inductive predicate on `List.Vector ℕ n →. ℕ`, which is
  what `Turing.ToPartrec.Code.exists_code` consumes;
* `Turing.ToPartrec.Code.eval : Code → List ℕ →. List ℕ`, which is what it
  produces.

`Nat.Partrec'.part_iff₂` is the bridge between the first two, and it is stated
for `f : ℕ → ℕ →. ℕ` -- so the universal function has to be presented with a
*numeral* first argument rather than a `Nat.Partrec.Code` one.  That is
`universalPartial`, which composes `eval` with `Denumerable.ofNat`.  Everything
else is bookkeeping.

## What is delivered

`universalCode` is one fixed `Turing.ToPartrec.Code` with

  `universalCode.eval [a, n] = pure <$> Nat.Partrec.Code.eval (ofNat _ a) n`,

so running it on `[a, n]` is running the `a`-th partial recursive function on
`n` (`universalCode_eval`).  Its halting problem is undecidable
(`universalCode_halting_undecidable`), transported from
`ComputablePred.halting_problem` across `Denumerable.ofNat`.

`Turing.PartrecToTM2.tr` then runs it, by `tr_eval`, giving a fixed `TM2`
machine and a fixed starting configuration family whose halting is undecidable
(`universalMachine_halting_undecidable`).  That is U2.

## What is still owed

U3--U5 of `SemigroupWordProblem`, unchanged: `tr` has an infinite label type
and must be cut down along `codeSupp` to a machine with a `Fintype` of labels;
the `TM2 → TM1 → TM0` descent has to be related to a two-list tape, which is
the `ListBlank` quotient work; and the conclusion has to be drawn through
`halts_iff_presentedMonoid_eq`.  Nothing here shortens those.  In particular
**no declaration in this file certifies a manuscript statement**, and none is
used by any manuscript-facing theorem -- the corollary `cor:undecidable`
remains exactly as conditional as it was.
-/

namespace GroupApproximation

namespace UniversalCode

universe u

open Nat.Partrec (Code)

/-! ## The universal partial function, with a numeral index -/

/-- The universal partial function, indexed by a *numeral* rather than by a
`Nat.Partrec.Code`.  The numeral index is forced: `Nat.Partrec'.part_iff₂`, the
only bridge into the inductive predicate `Turing.ToPartrec.Code.exists_code`
consumes, is stated for `ℕ → ℕ →. ℕ`. -/
def universalPartial : ℕ → ℕ →. ℕ :=
  fun a n => Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code a) n

/-- The universal partial function is partial recursive in both arguments:
`eval_part` composed with the computable decoding of the index. -/
theorem universalPartial_partrec₂ : Partrec₂ universalPartial :=
  Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst) Computable.snd

/-- The same statement in the inductive form `Turing.ToPartrec.Code.exists_code`
consumes. -/
theorem universalPartial_partrec' :
    Nat.Partrec' fun v : List.Vector ℕ 2 =>
      universalPartial v.head v.tail.head :=
  Nat.Partrec'.part_iff₂.mpr universalPartial_partrec₂

/-! ## The code -/

/-- **U1.**  Some `Turing.ToPartrec.Code` evaluates the universal partial
function on the two-element input list. -/
theorem exists_universalCode :
    ∃ c : Turing.ToPartrec.Code, ∀ a n : ℕ,
      c.eval [a, n] = pure <$> universalPartial a n := by
  obtain ⟨c, hc⟩ := Turing.ToPartrec.Code.exists_code universalPartial_partrec'
  refine ⟨c, fun a n => ?_⟩
  have h := hc ⟨[a, n], rfl⟩
  simpa [List.Vector.head, List.Vector.tail] using h

/-- A fixed universal `Turing.ToPartrec.Code`. -/
noncomputable def universalCode : Turing.ToPartrec.Code :=
  exists_universalCode.choose

/-- Running `universalCode` on `[a, n]` runs the `a`-th partial recursive
function on `n`. -/
theorem universalCode_eval (a n : ℕ) :
    universalCode.eval [a, n] = pure <$> universalPartial a n :=
  exists_universalCode.choose_spec a n

/-! ## Undecidability of its halting problem -/

/-- The halting problem transported from `Nat.Partrec.Code` to its numeral
index.  A decision procedure for the numeral form would give one for the code
form by composing with `Encodable.encode`, which is computable. -/
theorem universalPartial_halting_undecidable (n : ℕ) :
    ¬ ComputablePred fun a : ℕ => (universalPartial a n).Dom := by
  intro h
  obtain ⟨inst, hcomp⟩ := h
  refine ComputablePred.halting_problem n ?_
  have hpull : ComputablePred fun c : Nat.Partrec.Code =>
      (universalPartial (Encodable.encode c) n).Dom := by
    letI : DecidablePred fun a : ℕ => (universalPartial a n).Dom := inst
    exact ⟨inferInstance, hcomp.comp Computable.encode⟩
  have hfun : (fun c : Nat.Partrec.Code =>
        (universalPartial (Encodable.encode c) n).Dom)
      = fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c n).Dom := by
    funext c
    rw [universalPartial, Denumerable.ofNat_encode]
  exact hfun ▸ hpull

/-- Mapping a `Part` does not change its domain. -/
theorem dom_map_iff {α β : Type u} (f : α → β) (x : Part α) :
    (f <$> x).Dom ↔ x.Dom := Iff.rfl

/-- **The halting problem of the fixed universal code is undecidable.** -/
theorem universalCode_halting_undecidable (n : ℕ) :
    ¬ ComputablePred fun a : ℕ => (universalCode.eval [a, n]).Dom := by
  intro h
  refine universalPartial_halting_undecidable n ?_
  have hfun : (fun a : ℕ => (universalCode.eval [a, n]).Dom)
      = fun a : ℕ => (universalPartial a n).Dom := by
    funext a
    rw [universalCode_eval]
    exact propext (dom_map_iff _ _)
  exact hfun ▸ h

/-! ## U2: the machine that runs it -/

/-- **U2.**  Mathlib's `tr` evaluates the fixed universal code.  Immediate from
`Turing.PartrecToTM2.tr_eval`. -/
theorem universalMachine_eval (a n : ℕ) :
    StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init universalCode [a, n])
      = Turing.PartrecToTM2.halt <$> (pure <$> universalPartial a n) := by
  rw [Turing.PartrecToTM2.tr_eval, universalCode_eval]

/-- The machine halts on `init universalCode [a, n]` exactly when the `a`-th
partial recursive function halts on `n`. -/
theorem universalMachine_dom_iff (a n : ℕ) :
    (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init universalCode [a, n])).Dom
      ↔ (universalPartial a n).Dom := by
  rw [universalMachine_eval]
  exact (dom_map_iff _ _).trans (dom_map_iff _ _)

/-- **A fixed Turing machine whose halting problem is undecidable.**  This is
the object `Computability.SemigroupWordProblem` records as missing; it closes
U1 and U2 of that debt, and nothing else. -/
theorem universalMachine_halting_undecidable (n : ℕ) :
    ¬ ComputablePred fun a : ℕ =>
      (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
        (Turing.PartrecToTM2.init universalCode [a, n])).Dom := by
  intro h
  refine universalPartial_halting_undecidable n ?_
  have hfun : (fun a : ℕ =>
        (StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init universalCode [a, n])).Dom)
      = fun a : ℕ => (universalPartial a n).Dom := by
    funext a
    exact propext (universalMachine_dom_iff a n)
  exact hfun ▸ h

end UniversalCode

end GroupApproximation
