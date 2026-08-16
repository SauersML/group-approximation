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

Manuscript location, by stable anchors only --- `non_mf_groups_exist.tex` is
under concurrent edit and line numbers drift:
`\subsection{Undecidability of MF recognition}` inside section
`sec:consequences`; the corollary is `\label{cor:undecidable}`; the discussion
paragraph begins "This corollary carries one classical literature input, used
only here" and ends after "No completeness of the word problem under many-one
reduction is needed, only its undecidability".

## What the manuscript prints

The paragraph opening the subsection, immediately before the corollary, reads:

> Lemma~\ref{lem:permanence}(1) and Theorem~\ref{thm:A} make MF a Markov
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

None of (a), (b), (c) is within reach today.  What this file supplies is
everything on either side of them: the group-theoretic premises that let the
Adian--Rabin theorem be invoked (`operatorMF_isMarkovProperty`) and the
recursion-theoretic inference performed after the construction is in hand
(`negativeSide_not_re_of_re_of_not_computablePred`).

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

What Mathlib does **not** have, and this repository does not have either:

* Any `Encodable`/`Primcodable` instance for `FreeGroup α` or for finite group
  presentations; there is no notion of a presentation *as a code*.
* Any definition of the word problem of a presentation, and no proof that it
  is recursively enumerable.
* Semi-Thue systems, Post canonical systems, or the undecidability of the
  word problem for finitely presented semigroups.
* Novikov--Boone, Higman embedding, or Adian--Rabin in any form.

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
* `AdianRabinReduction.transform`, `.transform_computable`, `.correct` ---
  **open**; these three fields *are* (a), the Adian--Rabin construction.
* `¬ComputablePred sourceProperty` --- **open**; with the source concretized
  this is literally (b), Novikov--Boone.

So the conditionality of `cor:undecidable` is **unchanged**: what the recent
work bought is that both ends of the reduction now have concrete referents
instead of parameters, and the remaining hypotheses are now the two named
theorems rather than abstract data.  The `markov` field was always metadata ---
`MarkovMFConsequences` says so in its own docstring --- so discharging it moves
no conditionality.  The claim-manifest row stays `literature-input`.

Two observations about the existing material, both acted on below:

1. `MarkovMFConsequences.negative_side_not_re` takes `¬REPred (¬source)` as a
   *hypothesis*.  The manuscript does not assume that; it **derives** it from
   "the positive side is r.e." plus "the problem is undecidable".  The missing
   inference is supplied here as
   `negativeSide_not_re_of_re_of_not_computablePred`, so the existing pullback
   can now be fed from the manuscript's actual premises.
2. The sentence "MF is a Markov property of finitely presented groups" was
   never stated as a single theorem; only its two halves existed.  It is
   `operatorMF_isMarkovProperty` here.

## Engineering assessment of the remaining debt

The debt is exactly (a), (b) and (c) above; the pullback and the two
group-theoretic inputs are already machine-checked, so nothing else stands
between the repository and `cor:undecidable`.  The corollary cannot be closed
without a formal Novikov--Boone theorem, and the manuscript's *specific*
Markov property admits no cheaper route than the general construction; see "No
cheaper route" below.  Sizes are for a Lean 4 / Mathlib development, counting
only new lines and assuming the Mathlib pieces listed above are reused.  D1 and
D2 belong to (c) and to making (a) expressible; D3 and D4 are (b); D5 is (a).

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

* **D4. Novikov--Boone: a finitely presented group with undecidable word
  problem.**  The standard modern route is the Boone--Britton group: a tower
  of HNN extensions over a free group whose Britton reductions mirror the
  semi-Thue derivations of D3, plus the "special words" lemma.  Mathlib's
  Britton's Lemma and HNN normal form are a genuine enabler here and remove
  what used to be the single largest sub-project; `PushoutI` supplies the
  amalgamated-product normal forms needed for the free-subgroup arguments.
  What remains is the bookkeeping of the tower and the two-directional
  correctness proof.  **~2500--5000 lines.**  Depends on D3.  This is the
  dominant cost and, to the best of current knowledge, has never been done in
  any proof assistant.

* **D5. The Adian--Rabin construction, effectively.**  Given the group of D4,
  a word `w`, and a fixed finitely presented `E`, build `P_w` with `G(P_w)`
  trivial for `w = 1` and `E ↪ G(P_w)` for `w ≠ 1`, and prove the transform
  computable.  Rabin's trick is a short chain of HNN extensions and free
  products; correctness again runs on Britton's Lemma, and the "collapse to
  the trivial group" half needs a careful induction.  **~1500--3000 lines.**
  Depends on D1 and D4.

* **D6. Assembly.**  Feed D5 into `MarkovMFConsequences.AdianRabinReduction`
  over `PresentationCodes.semantics`, discharge `¬ComputablePred
  sourceProperty` from D4, and discharge `¬REPred (¬source)` from D2 and D4
  via `negativeSide_not_re_of_re_of_not_computablePred` below.  **~100--200
  lines.**  Mechanical once D1--D5 exist; the interfaces already fit.

Total: on the order of **6000--11000 new lines**, i.e. a multi-month
single-developer project whose critical path is D3 → D4.  It is a genuine
formalization project in its own right, not a gap in this manuscript's own
mathematics.

### Cost of retracting the manuscript's self-declaration

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
construction (`negativeSide_not_re_of_re_of_not_computablePred`), and the
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
  forbidden : ∃ (E : Type) (instE : Group E),
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
and Theorem `thm:A` make MF a Markov property of finitely presented groups ---
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

The manuscript does not assume that the negative side of the source problem
fails to be recursively enumerable; it derives that from the positive side
being recursively enumerable together with undecidability.  The existing
`MarkovMFConsequences.negative_side_not_re` takes the derived statement as a
hypothesis, so this lemma is the missing link between the manuscript's actual
premises and that pullback. -/

/-- **Manuscript step** (`cor:undecidable` discussion, the sentence "the
instances with $w=1$ form a recursively enumerable set which, the word problem
being undecidable, is not recursive; hence the instances with $w\ne1$ form a
set that is *not* recursively enumerable"): a decision problem whose positive
side is recursively enumerable and which is undecidable has a negative side
that is not recursively enumerable.

This is the contrapositive of Post's theorem
(`ComputablePred.computable_iff_re_compl_re'`), and it is unconditional: no
reduction data and no group theory enter.  Applied to the word problem, whose
positive side is r.e. and which is undecidable by Novikov--Boone, it yields
the manuscript's "hence the instances with `w ≠ 1` form a set that is *not*
recursively enumerable"; the last sentence of the manuscript's discussion --
an enumeration of the non-MF presentations would make the word problem
decidable -- is the same implication read forwards. -/
theorem negativeSide_not_re_of_re_of_not_computablePred
    {α : Type u} [Primcodable α] {p : α → Prop}
    (hre : REPred p) (hundec : ¬ ComputablePred p) :
    ¬ REPred (fun a ↦ ¬ p a) :=
  -- MATHLIB-UNVERIFIED: `ComputablePred.computable_iff_re_compl_re'` is the
  -- only Mathlib name in this file that does not already occur in the
  -- corpus.  It was read from Mathlib source at the pinned revision
  -- (`Mathlib/Computability/RE.lean`, Post's theorem, the primed form taking
  -- no `DecidablePred`), so the flag is procedural, not a doubt.
  fun hneg ↦ hundec (ComputablePred.computable_iff_re_compl_re'.2 ⟨hre, hneg⟩)

end AdianRabinMarkovProperty
end GroupApproximation
