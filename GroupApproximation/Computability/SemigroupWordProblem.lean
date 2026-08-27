import GroupApproximation.Computability.SemigroupWordProblemPresentation

/-!
# Markov--Post: what is proved here, and exactly what is missing

This is the entry point of the four-module development

* `SemigroupWordProblemRewriting` --- string rewriting, Thue equivalence, and a
  determinism criterion;
* `SemigroupWordProblemMachine` --- a deterministic Turing machine and the
  semi-Thue system attached to it;
* `SemigroupWordProblemSimulation` --- the two-directional simulation;
* `SemigroupWordProblemPresentation` --- the same statement inside Mathlib's
  `PresentedMonoid`,

whose target is the **Markov--Post theorem**: *the word problem for finitely
presented semigroups (monoids) is undecidable*.  What is proved *here* is its
reduction half, in full and unconditionally; the other half is a universal
machine.

**That half is no longer missing, though it arrived by a different route.**
`Computability.MarkovPost.exists_undecidable_wordProblem` proves Markov--Post
outright, with no hypothesis and no literature input, by composing
`Computability.UniversalMachineUndecidable` with the word encoding of
`Computability.FiniteMachineWordProblem` --- a `Turing.TM0` machine and the
`StringRewriting.PostMachine` system rather than the deterministic machine and
semi-Thue system developed in these four modules.  So the theorem holds; this
chain is a second, independent reduction that stops one step short of it, and
is retained because its simulation is stated for an arbitrary deterministic
machine.

## Manuscript context

`GroupApproximation/Computability/AdianRabinMarkovProperty.lean` records the
debt of the manuscript's undecidability corollary --- `\label{cor:undecidable}`
inside `\subsection{Undecidability of MF recognition}` of `sec:consequences` in
`non_mf_group_notes.tex` --- as items `D1`--`D5`, of which `D3` is
Markov--Post.  **No declaration in these four modules certifies a manuscript
statement**, and none is used by any manuscript-facing theorem.  They exist
because the manuscript's corollary rests, through Adian--Rabin and
Novikov--Boone, on the unsolvability of a word problem, and this repository
does not accept literature inputs.

## What is proved, unconditionally

Let `M : Machine Γ Λ` be a deterministic single-tape Turing machine
(configurations `⟨left, state, right⟩`, blanks off both ends) and let
`encCfg M c` be the word encoding the configuration `c` over the alphabet
`Letter Γ Λ`.

* `machine_isLocal` --- the rewriting system attached to `M` satisfies the
  seven structural conditions of `IsLocal`.  Consequently (`Step.det`) one-step
  rewriting is a **partial function** on words of weight one, and those words
  are closed under rewriting in both directions (`Step.weight_eq`).
* `thueEquiv_iff_derives` --- hence Church--Rosser: a two-sided Thue
  equivalence into a normal form is already a one-sided derivation.  No
  critical-pair or Newman machinery is used, and no confluence hypothesis is
  assumed.
* `halts_iff_thueEquiv` --- **`M.Halts c ↔ ThueEquiv … (encCfg M c) [done]`**,
  both directions.
* `halts_iff_presentedMonoid_eq` --- the same statement as an equality in
  `PresentedMonoid (machRels M)`.
* `machine_rules_finite` and `Letter.instFinite` --- for finite `Γ` and `Λ` the
  presentation has finitely many generators and finitely many relations, so the
  monoid above really is finitely presented.

Nothing in the four modules has a hypothesis standing in for a theorem, and in
particular there is no declaration of the form "if halting is undecidable then
the word problem is undecidable": such a statement would be a conditional
capstone, and this repository does not state those.

## What is missing: a universal machine

Markov--Post needs, beyond the reduction above, a **single** machine whose
halting problem is undecidable --- equivalently, a universal machine in this
model.  This is unavoidable and is not an artefact of the model chosen here:
undecidability of any property of a machine model forces that model to be
universal.  The same gap is the only gap in the Aanderaa--Cohen modular-machine
route to Novikov--Boone (Simpson's Theorem 4), so the work below is shared, not
specific to semigroups.

Mathlib supplies more of it than one might expect.  All of the following were
read from Mathlib source at the revision this project pins
(`lake-manifest.json` records `905b95818eb32af7874a58b427f50c1711a5e96c`,
`v4.32.2`); the line numbers are from that checkout.

* `Nat.Partrec.Code.eval_part : Partrec₂ eval` (`Computability/PartrecCode.lean:994`)
  --- the universal partial function is partial recursive.
* `Nat.Partrec.Code.exists_code` (`Computability/PartrecCode.lean:533`).
* `Turing.ToPartrec.exists_code` (`Computability/TuringMachine/Config.lean:267`)
  --- every `Nat.Partrec'` function is realised by a `ToPartrec.Code`.
* `Turing.PartrecToTM2.tr_eval` (`Computability/TuringMachine/ToPartrec.lean:940`)
  --- one `TM2` machine `tr` evaluates *every* code:
  `eval (TM2.step tr) (init c v) = halt <$> Code.eval c v`.
* `Turing.PartrecToTM2.tr_supports` and `codeSupp`
  (`.../ToPartrec.lean:1278`, `:1040`) --- `tr`'s label type is infinite (it
  embeds `Code` in the state) but is supported on a *finite* set of labels for
  each fixed code.
* `Turing.TM0`, `TM1`, `TM2` and the reductions `TM0to1`, `TM1to0`, `TM1to1`,
  `TM2to1` (`Computability/TuringMachine/PostTuringMachine.lean`,
  `StackTuringMachine.lean`).
* `ComputablePred.halting_problem` and `halting_problem_not_re`
  (`Computability/Halting.lean:65`, `:68`).

So the remaining work is glue, in this order.  Sizes are new Lean lines,
assuming the above are reused and counting no re-proof of Mathlib.

* **U1. A fixed universal code.  DONE**, in `Computability.UniversalCode`:
  `universalCode` is one `Turing.ToPartrec.Code` with `universalCode.eval
  [a, n] = pure <$> Nat.Partrec.Code.eval (ofNat _ a) n`, and
  `universalCode_halting_undecidable` says its halting problem is undecidable.
  The plumbing was as expected -- `Nat.Partrec'.part_iff₂` is stated for
  `ℕ → ℕ →. ℕ`, so the universal function has to carry a *numeral* index and
  the code index is decoded by `Denumerable.ofNat`; the halting problem is then
  transported off `Nat.Partrec.Code` along `Encodable.encode`.
* **U2. The machine for `c_U`.  DONE**, same module:
  `universalMachine_halting_undecidable`.  Immediate from `tr_eval`, as
  predicted.
* **U3. Cut the machine down to a finite one.**  `tr` has an infinite label
  type; restrict it along `codeSupp c_U Cont'.halt` (using `tr_supports`) to a
  machine with a `Fintype` of labels, and transport the evaluation statement.
  **~200--400 lines.**  Moderate risk: the `Supports` API is designed for this,
  but the restricted machine has to be built by hand.
* **U4. Bridge to a two-list tape.**  Descend `TM2 → TM1 → TM0` with Mathlib's
  reductions, then relate `Turing.Tape`/`ListBlank` (a quotient of lists by
  trailing blanks) to the `Cfg Γ Λ` of `SemigroupWordProblemMachine`.  This is
  the quotient work deliberately avoided when writing the simulation, and it
  has to be done exactly once, here.  **~400--800 lines.**  Highest risk item.
* **U5. Conclude.**  `¬ ComputablePred (fun x => M_U.Halts (initial x))` from
  `ComputablePred.halting_problem`, and then, with `halts_iff_presentedMonoid_eq`
  and a `Primcodable` structure on words, the undecidability of the word
  problem of `MachineMonoid M_U`.  **~100--200 lines.**  The `Primcodable`
  layer for `Letter Γ Λ`-words is the only genuinely new piece; it is the same
  kind of object as `PresentationCodes.PresentationCode`.

Total **~900--1700 lines**, critical path U1 → U3 → U4.  Until U1--U5 exist,
Markov--Post itself stays **MISSING** in this repository, and only the
reduction above is available.

## Two things deliberately not done

* **No conditional capstone.**  The theorem "if some machine in this model has
  undecidable halting then some finitely presented monoid has undecidable word
  problem" is true, short, and would be a hypothesis standing in for the
  missing mathematics.  It is not stated.
* **No `Primcodable` layer yet.**  Without U1--U4 there is nothing to feed it,
  and an encoding layer with no consumer invites exactly the kind of unused
  scaffolding that hides a gap.
-/
