import GroupApproximation.Computability.OperatorMFMarkovWitness
import Mathlib.Computability.RE

/-!
# The Adian--Rabin premises for MF recognition, and the exact remaining debt

This module certifies the *hypotheses* of the Adian--Rabin theorem for
operator-MF, and the recursion-theoretic inference that the manuscript makes
after the construction is available.  It does **not** assert the Adian--Rabin
theorem, the Novikov--Boone theorem, or any reduction data standing in for
them.  Nothing here is conditional: every declaration below is a closed
theorem with no premise that encodes an unformalized result.

Manuscript location, by stable anchors only --- `non_mf_group_notes.tex` is
under concurrent edit and line numbers drift:
`\subsection{Undecidability of MF recognition}` inside section
`sec:consequences`; the corollary is `\label{cor:undecidable}`; the discussion
paragraph begins "This corollary carries one classical literature input, used
only here" and ends after "No completeness of the word problem under many-one
reduction is needed, only its undecidability".

## What the manuscript prints

The paragraph opening the subsection, immediately before the corollary, reads:

> Lemma~\ref{lem:permanence}(1) and the earlier non-MF endpoint make MF a Markov
> property of finitely presented groups: the trivial group is MF, and by
> subgroup heredity the finitely presented group $E$ embeds in no MF
> group.  The Adian--Rabin theorem \cite{Rabin58} therefore applies.

That sentence is exactly `operatorMF_isMarkovProperty` below, and it is now
machine-checked in full, including the isomorphism-invariance clause that the
prose leaves implicit.

The corollary `cor:undecidable` itself reads:

> There is no algorithm that decides, from a finite presentation, whether the
> presented group is MF.  By the effective form of the Adian--Rabin
> construction \cite{Rabin58}, the set of finite presentations of non-MF
> groups is not even recursively enumerable.

and the discussion paragraph that follows it pins the literature input down:

> What the construction supplies is a computable map taking an instance
> $(P,w)$ of the word problem of a fixed finitely presented group with
> undecidable word problem to a finite presentation whose group is trivial
> --- hence MF --- when $w=1$, and contains $E$ --- hence non-MF, by subgroup
> heredity --- when $w\ne1$.  The instances with $w=1$ form a recursively
> enumerable set which, the word problem being undecidable, is not recursive;
> hence the instances with $w\ne1$ form a set that is *not* recursively
> enumerable. [...] No completeness of the word problem under many-one
> reduction is needed, only its undecidability.

The manuscript declares one literature input; read against what the corollary
actually deduces, that input resolves into two named theorems plus one silent
premise:

* **(a) The effective Adian--Rabin construction, one instance.** A computable
  map `w ↦ P_w` on words of a fixed finitely presented group with `G(P_w)`
  trivial when `w = 1` and `E ↪ G(P_w)` when `w ≠ 1`, where `E` is this
  repository's finitely presented non-MF group.
* **(b) Novikov--Boone.** There *is* a fixed finitely presented group whose
  word problem is undecidable.  **Undecidability only.**  The manuscript is
  explicit that no many-one completeness of the word problem is needed, and
  that matters: it means the missing input is the bare existence statement,
  not any degree-theoretic strengthening of it, and (a) is what carries the
  reduction.
* **(c) The word problem of a finite presentation is recursively enumerable.**
  Used silently in "the instances with $w=1$ form a recursively enumerable
  set".  This is *not* implied by (b): undecidability alone gives
  non-recursiveness, and the corollary's second sentence --- the set of non-MF
  presentations is not even recursively enumerable --- needs the positive side
  to be r.e. as well.  It is by far the smallest of the three, and it is
  classical (a recursively presented group has r.e. word problem), but it is
  load-bearing and must not be omitted from the ledger.

**(b) is done as of 2026-08-16**, unconditionally and with no literature
input: `Computability.NovikovBoone.exists_finitelyPresented_wordProblem_not_computablePred`.
**(a) is half done as of 2026-08-17**: its correctness clause is
`AdianRabinVariantTransform.correct`, hypothesis-free, and what remains of it is
`Computable transform` alone.  (c) has its mathematical half proved in
`AdianRabinWordProblem` and only `Primrec` plumbing left.  But see D4 and D6
below before assuming (b) can simply be handed to the assembly step: the
statement proved is about an abstract group, and the assembly needs a code.  What this file
supplies is everything on either side of them: the group-theoretic premises
that let the Adian--Rabin theorem be invoked (`operatorMF_isMarkovProperty`)
and the recursion-theoretic inference the manuscript performs once the
construction is in hand (`computablePred_of_re_of_negativeSide_re`).

Nothing here, and nothing in `AdianRabinWordProblem`, states a theorem whose
hypotheses include an undecidability assertion or a reduction-data package.
The capstone that would need one is deliberately absent; the debt is recorded
in prose instead.

## What Mathlib already has

Every name and absence below was read from Mathlib source at the revision this
project pins --- `lake-manifest.json` records
`905b95818eb32af7874a58b427f50c1711a5e96c` (`v4.32.2`), and the checkout read
was at exactly that commit.  Nothing in this section is recalled or guessed.

Computability:

* `ComputablePred`, `REPred`, `Partrec`, `Primrec`, `Primcodable`
  (`Mathlib/Computability/RE.lean`, `Primrec.lean`, `Partrec.lean`).
* `Nat.Partrec.Code` with `Denumerable Code`, `eval`, `evaln`, the recursion
  theorem, and Rice's theorem (`Mathlib/Computability/PartrecCode.lean`,
  `Halting.lean`).
* The halting problem: `ComputablePred.halting_problem_re`,
  `ComputablePred.halting_problem`, `ComputablePred.halting_problem_not_re`.
  So the *source undecidability* the manuscript needs is available in Mathlib
  for the halting problem; what is missing is a reduction landing in group
  presentations.
* Post's theorem, `ComputablePred.computable_iff_re_compl_re'`.
* Many-one reducibility and degrees (`Mathlib/Computability/Reduce.lean`:
  `ManyOneReducible` with notation `≤₀`, `OneOneReducible` with `≤₁`,
  `ManyOneReducible.mk`, `computable_of_manyOneReducible`, and the quotient
  `ManyOneDegree`), Turing degrees (`TuringDegree.lean`, `RecursiveIn.lean`).
  This is the idiomatic vocabulary for step D6 below; `MarkovMFConsequences`
  currently reproves the pullback by hand.
* Turing machines in namespace `Turing` and their equivalence with partial
  recursive functions: `Mathlib/Computability/TuringMachine/` (`Tape.lean`,
  `Config.lean`, `PostTuringMachine.lean`, `StackTuringMachine.lean`,
  `ToPartrec.lean`, `Computable.lean`), with top-level shims
  `TuringMachine.lean`, `PostTuringMachine.lean`, `TMToPartrec.lean`,
  `TMComputable.lean`.

Combinatorial group theory:

* `PresentedGroup`, `FreeGroup` with reduced words, `Group.IsFinitelyPresented`
  and `Subgroup.IsFinitelyNormallyGenerated`
  (`Mathlib/GroupTheory/PresentedGroup.lean`, `FinitelyPresentedGroup.lean`).
* HNN extensions **with normal form and Britton's Lemma**
  (`Mathlib/GroupTheory/HNNExtension.lean`:
  `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`).
* Amalgamated free products with normal form (`GroupTheory/PushoutI.lean`)
  and free products (`GroupTheory/CoprodI.lean`).

What Mathlib does **not** have (this repository has since supplied the first
two, as noted):

* Any `Encodable`/`Primcodable` instance for `FreeGroup α`, and no `Primrec`
  lemma about free reduction (`FreeGroup.reduce`, `FreeGroup.toWord`).  There
  is no notion in Mathlib of a presentation *as a code*; `PresentationCodes`
  supplies one here.
* Any definition of the word problem of a presentation; `AdianRabinWordProblem`
  supplies one here, with its certificate characterization.  Neither Mathlib
  nor this repository proves it recursively enumerable.
* Semi-Thue systems, Post canonical systems, or the undecidability of the
  word problem for finitely presented semigroups.
* Novikov--Boone, Higman embedding, or Adian--Rabin in any form.

The `Primrec` API for lists, by contrast, is rich enough for what remains of
(c) --- verified present at the pinned revision in
`Mathlib/Computability/Primrec/List.lean`: `list_foldl`, `list_rec`,
`list_append`, `list_concat`, `list_cons`, `list_length`, `list_take`,
`list_drop`, `list_takeWhile`, `list_dropWhile`, `list_getElem?`, `list_getD`,
`list_getI`.  That is exactly the toolkit the deletion-derivation route needs.

## What this repository already had

`GroupApproximation/Computability/`:

* `MarkovMFConsequences.lean` -- the generic many-one pullback, quantified
  over an explicitly supplied `AdianRabinReduction` (transform + correctness)
  and an assumed `¬ComputablePred sourceProperty`.  Every MF-facing conclusion
  there is conditional on that supplied data, which is precisely (a) and (b).
* `OperatorMFMarkovWitness.lean` -- the unconditional group-theoretic
  witnesses: `positive_punit` and `chosen_forbidden_subgroup`.
* `CStarRecognitionConsequences.lean` -- the same conditional pattern for the
  five group-C\*-algebra recognition predicates.
* `PresentationCodes.lean` (commit `fbfd635c`, added concurrently) -- a concrete
  `Primcodable` code type `ℕ × List (List (ℕ × Bool))` for finite
  presentations, its interpretation as a `PresentedGroup` over `Fin n`, and
  the resulting `FinitePresentationSemantics`.  That discharges the *ambient
  data* half of step D1 below; the `Primrec` lemmas for syntactic operations
  on codes, and everything downstream, remain open.
* `PresentationCodeCompleteness.lean` (added concurrently) -- adequacy of that
  coding (`exists_code_mulEquiv`: every finitely presented group is named by
  some code) and, from it, `markovWitness`.

### Which parameters of the badged endpoint are now discharged

`MarkovMFConsequences.operatorMF_recognition_undecidable` is quantified over
`Source`, `Code`, two `Primcodable` instances, `sourceProperty`, `semantics`,
an `AdianRabinReduction`, and `¬ComputablePred sourceProperty`.  Current state:

* `Code`, `Primcodable Code`, `semantics` --- **discharged**
  (`PresentationCodes`).
* `AdianRabinReduction.markov` --- **discharged**
  (`PresentationCodes.markovWitness`).
* `Source`, `Primcodable Source`, `sourceProperty` --- **discharged**
  (`AdianRabinWordProblem.wordProblemPred` on
  `PresentationCode × List (ℕ × Bool)`).
* `AdianRabinReduction.transform` and `.correct` --- **discharged**
  (2026-08-17, `Computability.AdianRabinVariantTransform`).  `correct` reads
  `operatorMFProperty semantics (transform x) ↔ WordProblem x.1 x.2`, with no
  hypothesis and no literature input: the transform free-products the input
  code with the fixed non-MF code and runs the variant construction, and the
  two directions are the collapse clause (the word dies, the output presents a
  free group, which is residually finite, hence MF) and the embedding clause
  (the word survives, the free product embeds, so its non-MF factor does).
* `AdianRabinReduction.transform_computable` --- **open, and now the whole of
  (a)**.  Note the shape of what is left: `transform` is a *`noncomputable`
  def*, so `Computable transform` is not a proof away, it needs a computable
  definition together with a proof that the two agree.  This is the same
  Prop-versus-coordinates gap as D4' below, and the same one the D3 entry flags
  about its own presentation being noncomputable.
* `¬ComputablePred sourceProperty` --- **open, but no longer for want of (b)**.
  Novikov--Boone is proved (D4).  What is missing is the passage from it to
  *this* predicate, which quantifies over `PresentationCode`s: see D6.

So the conditionality of `cor:undecidable` is **unchanged**: what the recent
work bought is that both ends of the reduction now have concrete referents
instead of parameters, and the remaining hypotheses are now the two named
theorems rather than abstract data.  The `markov` field was always metadata ---
`MarkovMFConsequences` says so in its own docstring --- so discharging it moves
no conditionality.  The claim-manifest row stays `literature-input`.

Two observations about the existing material, both acted on below:

1. `MarkovMFConsequences.negative_side_not_re` takes `¬REPred (¬source)` as a
   *hypothesis*.  The manuscript does not assume that; it **derives** it, from
   "the positive side is r.e." plus "the problem is undecidable".  The missing
   inference is `computablePred_of_re_of_negativeSide_re` below, stated in the
   forward direction the manuscript actually argues in, so that no declaration
   here carries an undecidability premise.  A future capstone contraposes it
   against (b).
2. The sentence "MF is a Markov property of finitely presented groups" was
   never stated as a single theorem; only its two halves existed.  It is
   `operatorMF_isMarkovProperty` here.

## Engineering assessment of the remaining debt

The debt was (a), (b) and (c) above; as of 2026-08-17 what is left of it is
**three computability obligations and nothing group-theoretic**: `Computable
transform` (the rest of (a)), `¬ComputablePred wordProblemPred` (D4', the coded
form of (b)), and the `Primrec` plumbing of (c).  Every group-theoretic input
the corollary needs is now machine-checked.  The older reading follows; as of
2026-08-16 the debt was **(a) and (c)**,
since (b) is proved.  The pullback and the two group-theoretic inputs are
already machine-checked, so nothing else stands between the repository and
`cor:undecidable`.  The corollary could not be closed without a formal
Novikov--Boone theorem, which is why D4 was the first thing built once D3
landed; and the manuscript's *specific* Markov property admits no cheaper route
than the general construction; see "No cheaper route" below.  Sizes are for a
Lean 4 / Mathlib development, counting only new lines and assuming the Mathlib
pieces listed above are reused.  D1 and D2 belong to (c) and to making (a)
expressible; D3 and D4 are (b); D4' is the passage from (b) to the coded form
the assembly consumes; D5 is (a).

* **D1. A presentation-code layer.**  `Primcodable` for finite presentations
  over a countable generating alphabet: a code type, the semantic map to
  `PresentedGroup`, and `Primrec` lemmas for the syntactic operations
  (concatenation, inversion, relabelling, disjoint union of presentations).
  The code type and its semantics now exist in `PresentationCodes.lean`;
  Mathlib's `Primcodable` instances for `ℕ`, `Bool`, products and lists carry
  the encoding side, but the free-group side needs `Primrec` facts about free
  reduction that do not exist anywhere.  **~200--450 lines remaining.**  No
  mathematical risk, high tedium.

* **D2. The word problem is recursively enumerable.**  For a presentation code
  `P`, the set of words trivial in `G(P)` is r.e.  **The mathematical half is
  now done**, in `AdianRabinWordProblem`: `mem_normalClosure_iff` characterizes
  the normal closure as the finite products of conjugates of relators and
  their inverses, and `wordProblem_iff_exists_rawCertificate` restates the word
  problem as an existential over a `Primcodable` certificate type.  (Mathlib
  turned out **not** to have `Subgroup.exists_list_of_mem_closure` --- only the
  `Submonoid` and `Subring` versions --- so that lemma is proved there too.)
  What remains is `Primrec` bookkeeping for the certificate checker plus the
  `FreeGroup.Red` equivalence "freely trivial iff some deletion sequence
  reaches `[]`".  **~250--450 lines remaining.**  Depends on D1.

* **D3. Undecidability of the word problem for finitely presented
  semigroups** (Markov--Post).  Simulate a Turing machine, or Mathlib's
  `Nat.Partrec.Code` via `TMToPartrec`, by a semi-Thue system; prove both
  directions of the simulation.  **~1000--2000 lines.**  This is the first
  step with real mathematical content, and the direction "the Thue system
  derives `q_0 w → q_halt` only if the machine halts" is the expensive half.
  Depends on D1 (for the reduction to be computable), not on D2.

  **DONE (2026-08-16).**  `Computability/MarkovPost.lean`,
  `PostMachine.exists_undecidable_wordProblem`: finite alphabets and a finite
  rewriting system over them whose word problem --- equality against one fixed
  four-letter word --- is undecidable.  No hypothesis and no literature input;
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, so the
  incomplete-proof axiom does not appear in the closure at all.  The route is
  the one this entry names, `TMToPartrec`:
  `UniversalCodeHalting` (a code whose halting is undecidable) →
  `UniversalMachineInit` (`PartrecToTM2 → TM2to1 → TM1to0` composed, the
  initialisation aligned by *choosing* the `Inhabited` instance) →
  `UniversalMachineUndecidable` → `MachineRestrict` (finitely many reachable
  states become finitely many states) → `FiniteMachineWordProblem` →
  `MarkovPost`.  The simulation itself is `PostMachine`/`PostMachineHalting`,
  where the expensive half this entry flags is `hstep_complete` together with
  `hstep_closed_inv`.

  Two corrections to this entry, in the interest of the ledger being usable:
  the finiteness of the state set --- which looked like the obstacle --- is
  already in Mathlib as `TM0.Supports` plus the `tr_supports` chain, and
  `TM0.Supports M S` unfolds to exactly the hypothesis the reduction needs.  And
  the dependence on D1 is not what was expected: the *rules* are a computable
  `flatMap` over enumerations, but the final presentation is noncomputable,
  because the TM0 state type contains `TM1.Stmt`, which contains function types
  and so has no decidable equality.  That costs nothing here --- "finitely
  presented" asks for a finite list of rules, not a computable one --- but a
  reduction that needs the *map to presentations* to be computable, as D5 does,
  cannot use this presentation as-is.

  Note also `Computability/SemigroupWordProblem{,Machine,Simulation,Presentation}`,
  which proves the same simulation independently and states it inside Mathlib's
  `PresentedMonoid`; it lacks only the universal machine, which is what the
  chain above supplies.

* **D4. Novikov--Boone: a finitely presented group with undecidable word
  problem.**  **The group and its correctness are DONE; what is left is
  finite presentability.**  The route taken is not Boone--Britton but
  Aanderaa--Cohen's modular machines, in Simpson's form: base group
  `⟨t, x, y | xy = yx⟩`, one HNN stable letter per machine quadruple, then one
  more letter `k`.
  * `BooneGroupGoodness.conj_k_finalTw_eq_iff` is the two-directional
    correctness statement, for an **arbitrary** modular machine and with no
    hypothesis: in `G_M`, `k` commutes with `t(α,β)` exactly when `(α,β)`
    halts.  Its inputs are Simpson's Lemma 5 (S2/S5a), the good-subgroup
    lemma (S4, from Mathlib's Britton), Lemma 7 (S6), and Britton for the
    single letter `k` (S7).
  * `Computability.ModularMachineUndecidable` supplies a machine whose halting
    set is not computable --- the input Simpson leaves to the reader --- by
    reading a modular machine as a two-stack machine and running a `TM0` on it.
  * `BooneGroup.exists_group_wordProblem_not_computablePred` is the two
    together: a group and a sequence of words in it for which triviality is not
    decidable.  Axiom-clean.
  **DONE (2026-08-16).**  S8 --- that `G_M` is finitely presented --- is
  `BooneGroupFinitePresentation.finalGroup_isFinitelyPresented`, and
  `NovikovBoone.exists_finitelyPresented_wordProblem_not_computablePred` is the
  conjunction of the two halves over the same `FinalGroup mm hM`.  Axiom-clean,
  no hypothesis, no literature input.

  The estimate above was **~500--900 lines**; it came to about 300, because the
  entry mis-stated the obstacle.  Mathlib does not need a presentation
  `⟨X, s | R, s aᵢ s⁻¹ = bᵢ⟩` to be built and proved to present the extension:
  it *defines* `HNNExtension G A B φ` as a quotient of `G ∗ Multiplicative ℤ`,
  and already closes `IsFinitelyPresented` under `Monoid.Coprod` and under
  quotient by a `Subgroup.IsFinitelyNormallyGenerated`.  So the whole content
  is cutting the relation family `{t a t⁻¹ (φ a)⁻¹ : a ∈ A}` down to a
  generating set, which is `MonoidHom.eq_of_eqOn_dense` applied to two homs
  `A →* Q`.  **Britton's Lemma is never used** in this half.  The half that
  could have failed was instead that `⟨t⟩'` --- free of infinite rank in the
  base group --- is finitely generated *in the tower*, one generator per stage.
  See `Algebra.HNNFinitePresentation`.

* **D5. The Adian--Rabin construction, effectively.**  Given the group of D4,
  a word `w`, and a fixed finitely presented `E`, build `P_w` with `G(P_w)`
  trivial for `w = 1` and `E ↪ G(P_w)` for `w ≠ 1`, and prove the transform
  computable.  Rabin's trick is a short chain of HNN extensions and free
  products; correctness again runs on Britton's Lemma, and the "collapse to
  the trivial group" half needs a careful induction.  **~1500--3000 lines.**
  Depends on D1 and D4.

  **The correctness half is DONE (2026-08-17)**, in
  `Computability.AdianRabinVariantTransform.correct`, hypothesis-free and
  axiom-clean.  The construction is the variant tower, whose embedding half was
  itself made unconditional the same day by describing stage 1 as
  `HNNExtension Γ ⊥ ⊥` rather than `Monoid.Coprod Γ ℤ` --- the same group, said
  so that Britton applies, after which every word in the stable letter is
  Britton-reduced and `⁅w, s⁆` has infinite order rather than being assumed to.
  The estimate above was not wrong about the mathematics; what shortened it is
  that the collapse induction runs on relabelling lemmas
  (`PresentedGroupRelabel.congrEquiv`, `HNNCongr.congrEquiv`) instead of on a
  bespoke normal form.

  **What is left of D5 is exactly `Computable transform`**, and it is not a
  small residue of the same kind: see the parameter list above.  A
  `noncomputable def` cannot be shown `Computable`; the obligation is to give
  the transform a computable definition and prove it agrees with this one.

* **D6. Assembly.**  Feed D5 into `MarkovMFConsequences.AdianRabinReduction`
  over `PresentationCodes.semantics`, discharge `¬ComputablePred
  sourceProperty` from D4, and discharge `¬REPred (¬source)` from D2 and D4
  via `computablePred_of_re_of_negativeSide_re` below.  **~100--200
  lines.**  Mechanical once D1--D5 exist; the interfaces already fit.

  **Correction (2026-08-16), now that D4 is done: "discharge `¬ComputablePred
  sourceProperty` from D4" is not mechanical, and the gap is not plumbing.**
  `sourceProperty` is `wordProblemPred` on `PresentationCode × List (ℕ × Bool)`,
  where `PresentationCode = ℕ × List (List (ℕ × Bool))` is concrete data.  D4
  delivers `Group.IsFinitelyPresented (FinalGroup mm hM)`, which in Mathlib is
  a `Prop`-valued class --- `∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G),
  Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated`.  Choice extracts `n`, `φ`
  and a finite relator set from it, so a code `c₀` for the group does exist;
  that much is fine, and a constant function at a noncomputable value is still
  computable.  What choice does *not* give is the other half of the reduction:
  the undecidable sequence in D4 is a sequence of group **elements**
  `g : ℕ → FinalGroup mm hM`, and to contradict computability of
  `wordProblemPred` one needs a **computable** `w : ℕ → List (ℕ × Bool)` with
  `wordOf c₀ (w m)` trivial exactly when `g m = 1`.  Preimages under a chosen
  `φ` carry no such guarantee.

  So D6 acquires a genuine predecessor, which is not D5 and not hard, but is
  not nothing:

  * **D4'. The Boone group as an explicit code.**  Exhibit `c₀ :
    PresentationCode` presenting `FinalGroup mm hM` --- the relators are
    explicit in the machine, one HNN stable letter per quadruple plus `k` ---
    together with a computable `w` spelling out the words
    `t⁻¹ · finalTw · t · finalTw⁻¹` in `c₀`'s generator numbering, and prove
    the two agree.  Then `¬ComputablePred wordProblemPred` is immediate.

    **Status 2026-08-17, evening: all four pieces are done and the join is
    instantiated --- D4' is closed.**

    - *The undecidable source, in the form the group side can use* --- **done**,
      `ModularMachineConfigHalting.exists_modularMachine_config_halting_not_computablePred`:
      `∃ mm, ¬ComputablePred fun p : ℕ × ℕ => mm.Halts p`, axiom-clean.  Note
      this is on the machine's own *configurations*, with no indexing map, which
      is what lets the words be attached to `(i, j)` directly.  It needed the
      index map of `exists_modularMachine_halting_not_computablePred` to be
      computable, and that turned out **not** to require `Primrec` through
      `PartrecToTM2 → TM2to1 → TM1to0`: the map only ever builds an *initial*
      configuration, so `encCfg` of it is a constant beside a Horner fold, and
      the choice-based `Fintype.equivFin` contributes fixed naturals rather than
      needing evaluation (`BinaryDigitPrimrec`, `TrNatRecurrence`,
      `IndexMapComputable`).
    - *The code* --- **done**, `BooneGroupCode.finalGroupCodeEquiv`:
      `Carrier (finalGroupCode mm hM) ≃* FinalGroup mm hM`.  `BooneTowerPresentation`
      had presented the tower and adjoined `k` without ever saying the result was
      `FinalGroup`; the two are not definitionally equal, since the presentation's
      associated subgroup is its own `tsub` and agreement is `machineTowerPres_tsub`,
      an equality of subgroups appearing in the *type*.  `hnnCongrOfEq` transports
      it by `subst`.
    - *Coded triviality as a decidable search* --- **done**,
      `CodedWordTriviality.wordOf_eq_one_iff_exists_steps`.  `wordOf c w` lives in
      `FreeGroup (Fin (genCount c))`, a family depending on the code, and no
      dependent family is `Primcodable`; normalising letters mod `genCount c` and
      pushing along the injection `Fin.val` moves the question into `FreeGroup ℕ`,
      where the deletion certificate of `FreeGroupDeletion` decides it.
    - *The words* --- **done (2026-08-17), and with them D4' is CLOSED.**  Four
      modules, one per layer: `BooneWords` writes
      `k⁻¹ · t(α,β) · k · t(α,β)⁻¹` as raw data and proves the presentation
      reads it as the halting element (`equiv_commElt`);
      `BooneWordMapPrimrec.computable_rawComm` makes the configuration-to-word
      map computable (the four generator indices are fixed naturals, so
      `Primrec.const` carries them without evaluating);
      `BooneWordAgreement.wordProblem_rawComm_iff` reads the code's word
      problem on the raw word as `commElt P q = 1`, moving triviality across
      the renumbering without tracking elements through `stageCodeEquiv`; and
      `BooneWordProblemUndecidable` bridges to Simpson's Theorem 8 by stating
      it at a *variable* associated subgroup so `machineTowerPres_tsub` can be
      substituted, then instantiates the join.  The endpoints are
      `Computability.not_computablePred_wordProblemPred` --- the uniform word
      problem on presentation codes is undecidable, no hypothesis, no
      literature input --- and `Computability.operatorMF_recognition_not_computable`.

    The trap note below was right and is kept for the record: `stageCode` is
    `noncomputable`, and that is harmless.  The code is a fixed object, and a
    constant at a noncomputable value is still `Computable`; only the *word
    map* has to be effective.  Needing `stageCode` itself to compute would be
    a sign the statement had drifted.

  **This DOES now change the manuscript's conditionality** (the sentence above
  saying otherwise predates the close): with D4' discharged,
  `operatorMF_recognition_undecidable_of_wordProblem` fires and the positive
  clause of `cor:undecidable` is unconditional.  What remains conditional is
  only the negative-side clause, whose hypothesis is the r.e. half ((c)/D2's
  integration, `REPred wordProblemPred`).

Total: on the order of **6000--11000 new lines**, i.e. a multi-month
single-developer project whose critical path is D3 → D4.  It is a genuine
formalization project in its own right, not a gap in this manuscript's own
mathematics.  (The estimate above is the original one and has not been
rescaled.  As of 2026-08-16 **D3 and D4 are both done in full**, so the
critical path has moved to D5, with D1, D2 and the newly separated D4' as its
prerequisites.  D4 came in at roughly a third of its estimate; nothing licenses
assuming D5 will do the same, since its cost is in a Britton-based induction
rather than in a permanence property Mathlib turned out to already have.)

### Cost of retracting the manuscript's self-declaration

**Executed (2026-08-17).**  The retraction this section prices has since been
carried out: (a) was rebuilt as surgery on relator lists
(`AdianRabinVariantTransform`, ledger row UN.04), (b) closed as D3/D4, and the
D4' coordinates closed above, so the sentence this section is about is being
removed from the manuscript and the positive clause of `cor:undecidable` is
unconditional.  The paragraphs below are the original estimate, kept because
the reasoning about *why* there was no partial retraction was correct --- the
route taken is exactly the "whole 6000--11000 lines" it describes, which came
in cheaper than priced for the reasons recorded per-item above.  Only
(c)/D2's integration (the r.e. half, worth the quoted ~5%) is still open.

The manuscript says of `cor:undecidable`: "This corollary carries one classical
literature input, used only here: the Adian--Rabin construction itself, which
we have not formalized."  Retracting that sentence --- making the development
literature-free end to end --- costs D1 through D6 in full, i.e. the whole
6000--11000 lines, because the sentence names the single input on which the
whole corollary rests.  There is no partial retraction: closing (a) without
(b) is impossible (the construction has nothing to reduce from), and closing
(b) without (a) leaves the corollary exactly as conditional as it is now.  The
only genuinely separable piece is (c)/D2, which closes the difference between
"undecidable" and "not even recursively enumerable" and is worth roughly 5% of
the total.  Every step of the chain *outside* that sentence is already
machine-checked, which is why the sentence can be stated so narrowly.

## No cheaper route for the manuscript's specific Markov property

The question is whether "is MF" being *this particular* Markov property admits
a construction cheaper than general Adian--Rabin.  It does not.  Four candidate
shortcuts, all failing:

1. *Only one Markov property is needed, not all of them.*  True, but the
   Adian--Rabin construction is uniform in the forbidden group `E`;
   specialising it to this repository's `E` removes no step.  D5 costs the
   same for one `E` as for all.
2. *Use the halting problem as the source instead of the word problem.*  Not
   available: the reduction must produce **group presentations**, and its
   correctness is stated in terms of a group element being trivial.  Some
   finitely presented group with undecidable word problem is unavoidable, so
   D4 cannot be skipped by changing the source.
3. *Exploit MF-specific structure.*  MF is subgroup-hereditary and holds for
   all countable residually finite groups, so the positive side of the
   reduction may target any residually finite group rather than the trivial
   one.  Adian--Rabin already targets the trivial group, which is the
   strongest positive case; the weaker requirement buys nothing, because the
   difficulty is the *negative* side (forcing `E` to embed) together with the
   collapse dichotomy, not the choice of positive target.
4. *Use a finitely generated recursively presented group with undecidable word
   problem.*  Those are elementary to construct, but the manuscript's decision
   problem is over **finite** presentations, and bridging finitely generated
   recursively presented to finitely presented is Higman's embedding theorem,
   which is strictly harder than D4.

**Verdict: no.**  The cost of `cor:undecidable` is the cost of Adian--Rabin in
general, and the only real saving available is architectural --- Mathlib's
Britton's Lemma and HNN/amalgam normal forms did not exist a few years ago, and
they cut D4 and D5 substantially.  The one genuine simplification the
manuscript's own phrasing already banks is that (b) is needed only as
*undecidability*, not as many-one completeness or as a specific degree: D4 may
target any single finitely presented group whose word problem is undecidable,
with no uniformity or completeness obligation, which removes the hardest
optional strengthening of Novikov--Boone from scope.

## Honest status

`cor:undecidable` remains **MISSING** under this project's standard.  What is
now complete and unconditional is: the Markov-property premise
(`operatorMF_isMarkovProperty`), the subgroup-heredity step in the abstract
form the premise needs (`operatorMF_hereditary`, `forbidden_of_hereditary`),
the recursion-theoretic inference the manuscript performs after the
construction (`computablePred_of_re_of_negativeSide_re`), and the
mathematical half of the r.e.-ness premise (`AdianRabinWordProblem`).  What is
missing is (a) and (b) in full, and the `Primrec` half of (c).

A structural finding from doing D2, recorded because it constrains every later
step: `PresentationCodes.wordOf c` lands in `FreeGroup (Fin (genCount c))`, a
type **depending on the code**.  No `Primcodable` instance can exist for a
dependent type, so no search space of free-group certificates is one a partial
recursive function can range over.  Every computability statement about coded
presentations --- including the Adian--Rabin transform of step D5 --- has to be
phrased on raw word lists, with decoding total.  `AdianRabinWordProblem`
follows that discipline throughout.
-/

namespace GroupApproximation
namespace AdianRabinMarkovProperty

open ChosenMarkedPresentation ChosenNonMFTheorem OperatorMFMarkovWitness

universe u

/-! ## Markov properties of finitely presented groups -/

/-- A property of groups, in the shape consumed by the Adian--Rabin theorem: a
predicate on types equipped with a group structure.  The group structure is an
explicit argument so that isomorphism invariance can be stated without
implicit-instance ambiguity. -/
abbrev GroupProperty := ∀ (G : Type), Group G → Prop

/-- A *Markov property* of finitely presented groups, in the sense of
Adian--Rabin: an isomorphism-invariant property that some finitely presented
group has, and for which some finitely presented group embeds in no finitely
presented group having it.

This is the literature definition, stated verbatim; the third clause is
restricted to finitely presented targets exactly as in Adian--Rabin.  Nothing
in this repository asserts the Adian--Rabin theorem itself, which says that
every Markov property is undecidable on finite presentations. -/
structure IsMarkovProperty (P : GroupProperty) : Prop where
  /-- The property depends only on the isomorphism class. -/
  isoInvariant : ∀ (G H : Type) [instG : Group G] [instH : Group H],
      G ≃* H → P G instG → P H instH
  /-- Some finitely presented group has the property. -/
  positive : ∃ (G : Type) (instG : Group G),
      Group.IsFinitelyPresented G ∧ P G instG
  /-- Some finitely presented group embeds in no finitely presented group
  having the property. -/
  forbidden : ∃ (E : Type) (_instE : Group E),
      Group.IsFinitelyPresented E ∧
        ∀ (H : Type) [instH : Group H], Group.IsFinitelyPresented H →
          P H instH → ∀ f : E →* H, ¬ Function.Injective f

/-- The manuscript's derivation of the forbidden-subgroup clause: for a
subgroup-hereditary property, a group *failing* the property embeds in no
group *having* it.  This is the "by subgroup heredity the finitely presented
group `E` embeds in no MF group" step, isolated from MF. -/
theorem forbidden_of_hereditary {P : GroupProperty}
    (hereditary : ∀ (A B : Type) [instA : Group A] [instB : Group B]
      (f : B →* A), Function.Injective f → P A instA → P B instB)
    {E : Type} [instE : Group E] (hE : ¬ P E instE)
    {H : Type} [instH : Group H] (hH : P H instH) (f : E →* H) :
    ¬ Function.Injective f :=
  fun hf ↦ hE (hereditary H E f hf hH)

/-! ## Operator-MF is a Markov property -/

/-- Operator-MF packaged as a `GroupProperty`. -/
@[reducible] def operatorMFGroupProperty : GroupProperty :=
  fun (G : Type) (instG : Group G) ↦ @IsOperatorMF G instG

/-- Manuscript Lemma `lem:permanence`(1) in `GroupProperty` form: operator-MF
passes to subgroups, equivalently pulls back along injective homomorphisms. -/
theorem operatorMF_hereditary (A B : Type) [instA : Group A] [instB : Group B]
    (f : B →* A) (hf : Function.Injective f)
    (hA : operatorMFGroupProperty A instA) :
    operatorMFGroupProperty B instB := by
  have hA' : @IsOperatorMF A instA := hA
  exact IsOperatorMF.comap hA' f hf

/-- Operator-MF is invariant under group isomorphism. -/
theorem operatorMF_isoInvariant (G H : Type) [instG : Group G] [instH : Group H]
    (e : G ≃* H) (hG : operatorMFGroupProperty G instG) :
    operatorMFGroupProperty H instH := by
  have hG' : @IsOperatorMF G instG := hG
  exact IsOperatorMF.comap hG' e.symm.toMonoidHom e.symm.injective

/-- **Manuscript sentence opening
`\subsection{Undecidability of MF recognition}`:** Lemma `lem:permanence`(1)
and the earlier non-MF endpoint make MF a Markov property of finitely presented groups ---
the trivial group is MF, and by subgroup heredity the finitely presented group
`E` embeds in no MF group.

This is the complete hypothesis of the Adian--Rabin theorem, and it is
unconditional: the positive witness is the trivial group, and the forbidden
witness is this repository's finitely presented non-MF group, whose
non-MF-ness is `ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF`.
The conclusion of Adian--Rabin is *not* asserted anywhere in this
repository. -/
theorem operatorMF_isMarkovProperty : IsMarkovProperty operatorMFGroupProperty where
  isoInvariant := by
    intro G H instG instH e hG
    exact operatorMF_isoInvariant G H e hG
  positive :=
    ⟨PUnit.{1}, inferInstance, positive_punit.1, positive_punit.2⟩
  forbidden := by
    refine ⟨MarkedGroup, inferInstance,
      chosenFinitelyPresented_not_isOperatorMF.1, ?_⟩
    intro H instH _ hH f
    exact forbidden_of_hereditary (P := operatorMFGroupProperty)
      operatorMF_hereditary chosenFinitelyPresented_not_isOperatorMF.2 hH f

/-! ## The recursion-theoretic step of `cor:undecidable`

The manuscript's final inference is stated forwards: *"An enumeration of the
non-MF presentations would enumerate that set, making the word problem
decidable."*  That is the direction proved below, and it carries no
undecidability hypothesis --- both premises are positive recursive-enumerability
facts.  The manuscript's preceding half-sentence ("hence the instances with
`w ≠ 1` form a set that is not recursively enumerable") is this implication
contraposed against undecidability of the word problem, which is
Novikov--Boone and is *not* stated anywhere in this repository, as a theorem or
as a hypothesis.

`MarkovMFConsequences.negative_side_not_re` takes the contraposed statement as
a hypothesis.  The lemma below is what lets a future capstone reach that
hypothesis from the manuscript's actual premises, without anything in the
present corpus assuming undecidability. -/

/-- **Manuscript step** (`cor:undecidable` discussion, the sentence "An
enumeration of the non-MF presentations would enumerate that set, making the
word problem decidable"): a decision problem both of whose sides are
recursively enumerable is decidable.

Post's theorem, specialized to the direction the manuscript argues in.  Both
hypotheses are positive facts about an arbitrary predicate; no undecidability
premise, no reduction data, and no group theory enter. -/
theorem computablePred_of_re_of_negativeSide_re
    {α : Type u} [Primcodable α] {p : α → Prop}
    (hre : REPred p) (hnegre : REPred (fun a ↦ ¬ p a)) :
    ComputablePred p :=
  -- MATHLIB-UNVERIFIED: `ComputablePred.computable_iff_re_compl_re'` is the
  -- only Mathlib name in this file that does not already occur in the
  -- corpus.  It was read from Mathlib source at the pinned revision
  -- (`Mathlib/Computability/RE.lean`, Post's theorem, the primed form taking
  -- no `DecidablePred`), so the flag is procedural, not a doubt.
  ComputablePred.computable_iff_re_compl_re'.2 ⟨hre, hnegre⟩

end AdianRabinMarkovProperty
end GroupApproximation
