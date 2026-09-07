# Adversarial audit of the closed LIX chain (2026-09-07, lane `lix-hsq`)

Commissioned by the lead after `hsq` closed, on the principle that someone who
was not the lead should try to break `¬ ProblemLIX` before the repository stands
behind it.  Everything below was checked against the source or against a build,
never against a docstring; where I could not check something I say so.

**Verdict: I found nothing that breaks the result.**  The chain compiles end to
end, its endpoint is unconditional and classically clean, and the statement is a
faithful reading of the printed problem *given* the quotation in
`ProblemLIX.lean`, which is the one thing here I could not verify and the one
thing a human must.

## 0. The end-to-end check

Fresh build of the endpoint's whole closure in clone `cs-simplicity`:

```text
Build completed successfully (9346 jobs)      sorryAx: none
ProblemLIX.lean:378:21: 'NinetyNineProblems.not_problemLIX'
    depends on axioms: [propext, Classical.choice, Quot.sound]
ProblemLIX.lean:379:21: 'NinetyNineProblems.exists_separable_simple_unital_not_k1Inj'
    depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both lines sit at `#audit_closed_axioms` positions, so the closed gate ran and
did not throw: neither declaration has a leading binder.  Both axiom lines were
read **out of the remote log by declaration name**, not out of the probe's
summary — see finding F2 for why that distinction was not cosmetic.

## 1. Is `ProblemLIX` a faithful statement of the printed problem?

Clause by clause, each checked against the definition rather than the prose:

* **unital** — `CStarAlgebra` extends `NormedRing`
  (`Mathlib/Analysis/CStarAlgebra/Classes.lean`, verified in the source), so
  unitality carries no separate hypothesis.
* **nontrivial** — asked separately.  Adding a hypothesis *weakens* the
  universal and so *strengthens* its negation: the safe direction.
* **simple** — `IsSimpleCStar A := ∀ I : Ideal A, I.IsTwoSided → IsClosed ↑I →
  I = ⊥ ∨ I = ⊤`.  That is C⋆-simplicity, not Mathlib's algebraic
  `IsSimpleRing`, and the endpoint says what the problem says.
* **`K₁`-injective** — `K1Inj A` is `K1Injective A` is
  `Function.Injective (kappa A)`, where `kappa = kOneIota 1 ∘ unitaryClassOneByOne`
  maps `U(A)/U₀(A)` into `KOne A`, the colimit of `U(Mₙ(A))/U₀(Mₙ(A))` along
  `u ↦ diag (u, 1)`, and `unitaryComponentOne = Subgroup.pathComponentOne`.
  This **is** the canonical map, defined the standard way.
* **universe** — quantified over `Type`, not `Type u`.  Weaker universal,
  stronger negation: again the safe direction, and the counterexample is a
  concrete separable algebra in `Type 0`.

Two claims the header makes about its own genericity, both verified: the three
modules under `CStarKOne` (`SequentialGroupColimit`, `CStarUnitaryComponent`,
`CStarMatrixBlockInclusion`) import only `Mathlib.*`; and
`isSimpleCStar_iff_isSimpleRing` really is landed (`CStarSimple.lean:158`) and
not merely promised.

## 2. Is anything vacuous?

The place a refutation of this shape can rot is `LemmaTwoHolds`, because it is a
**negation**: if `ContinuousMvNEquiv` were unsatisfiable for a silly reason, the
whole chain would rest on an empty predicate.  It is not.

* `ContinuousMvNEquiv P Q := ∃ w, Continuous w ∧ (∀ m, (w m)ᴴ * w m = P m) ∧
  (∀ m, w m * (w m)ᴴ = Q m)` — the standard notion, a genuine existential.
* The repository **constructs** elements of it:
  `LIX.continuousMvNEquiv_of_unitary_field` produces one from a continuous
  unitary field conjugating `EHmat` onto `FHmat`.  That is how Corollary 4 uses
  it — a null-homotopy of the stage unitary yields such a field, hence the
  equivalence, hence the contradiction.  A predicate the development can inhabit
  on the negation of the conclusion is not vacuous.
* `FHmat` and `EHmat` are not accidentally equal: `sProj` is `rankOneProj (bVec m)`,
  which varies with the point of `S⁵`, while `eProj` is the constant
  `rankOneProj eThree`.  Had they been equal the negation would have been *false*,
  not vacuous, and the development inconsistent.
* The counterexample algebra is real: `Nontrivial LIXLimit` by instance,
  `LIX.lixLimit_isSimpleCStar` and `LIX.lixLimit_separableSpace` unconditional
  theorems, and `HasK1InjWitness` an explicit `∃` around the constructed
  `genUnitary`.

**One prose claim in this area is true but unproved.**  `LIXLemmaTwoProp`'s
docstring says both projections have pointwise rank `2 + m`, "so this is not
refutable from the trace".  That is correct — `sProj` and `eProj` are rank-one
projections inside `V`, and both `bVec m` and `eThree` are unit vectors — but no
Lean declaration says it.  It is commentary on why the statement is hard, not a
step, so it is not a defect; it is also two lines from `trace_rankOneProj` if
anyone wants it certified.

## 3. Do the residues compose to what they claim?

* `lix_topClass_ne_zero_of_three`'s `hsq` binder and `CharClass.lixHsq` are
  **token-for-token identical** (compared mechanically, not by eye), and
  `LIXStepCOddHsq` applies the consumer at that binder, so the fit is a
  typechecked fact and not a resemblance.
* The Step C / Step D contradiction is about the *same object*: Step C's
  hypothesis and `lixStepD_unconditional`'s conclusion are both about
  `lixTopClass (lixChern (LIX.lixDD j)) (mappingTorus Vmat G circHoriz circHeight)`,
  head and arguments identical.  This is exactly where "green about different
  spaces" would bite, and it does not.  Step D is proved for every continuous
  corner-unitary `G` while Step C needs the seam condition too — the asymmetry
  is in the safe direction.
* Step A is **derived from the assumed equivalence** (`LemmaTwoStepA`), not
  carried as an extra hypothesis, which is what makes the proof by contradiction
  honest.

## 4. Findings

**F1 — an import cycle, real when found, already fixed.**  At 11:35 the shared
working tree had a two-module cycle: `ProblemLIX.lean` imported
`CharClass.LemmaTwoOfHsqHresHclass`, which then still carried a
`¬ ProblemLIX` corollary and so imported `ProblemLIX.lean`.  `lake` reported
`build cycle detected` and `bad import`.  `lix-wire` resolved it on origin
independently, by removing that corollary, and the current
`LemmaTwoOfHsqHresHclass` docstring records the constraint.  Recorded because
the constraint is load-bearing and easy to undo: **the module proving
`lemmaTwoHolds` may not mention `ProblemLIX`**, or the endpoint cannot import it.

**F2 — the probe's axiom section truncated exactly the endpoints.**
`lixprobe7.sh`'s per-file section ends in `head -40`, and an axiom list that
wraps costs three lines, so in a file with many audited declarations the *last*
ones are dropped — and by this repository's convention the last declarations are
the closed endpoints.  In my endpoint run the remote log held **91** axiom lines
and **14** reached the local log; among the missing were `not_problemLIX` and
`exists_separable_simple_unital_not_k1Inj`, the only two that matter.  Nothing
was wrong with the build; the report was silent about the thing it existed to
report.  The lead caught this independently and `lixprobe8.sh` supersedes.
The general shape is worth keeping: this is the same defect as the filtered
`info:` lines, one level up, and fixing a log filter does not fix a log
truncation.

**F3 — a docstring claim missing a hypothesis** (`ProblemLIX.lean`, not edited).
"The two agree for a unital C⋆-algebra" omits `Nontrivial`, which
`isSimpleCStar_iff_isSimpleRing` requires and needs: at the zero algebra
`IsSimpleCStar` holds vacuously (`⊥ = ⊤`) while `IsSimpleRing` fails, because
Mathlib's `IsSimpleOrder` extends `Nontrivial`.  Not load-bearing — the endpoint
uses `IsSimpleCStar` throughout and never the bridge — so it is reported rather
than edited, the more so because that file changed under me twice during the
audit.

**F4 — a generic lemma whose name outran its statement** (mine, fixed at
`2466fad6b`).  `injective_relPullback_subInclusion` reads as "restriction along
an inclusion of subspaces is injective", which is false in general; it holds
only because both sets are open neighbourhoods of the marked point and both
subspaces are that point's complement.  The header now says which hypotheses may
not be dropped.

**F5 — the one thing I could not check, and the one that would cost most.**
`ProblemLIX` omits **nuclearity**.  The paper is titled *Nuclear C⋆-algebras: 99
problems*, and `ProblemLIX.lean` quotes the problem as "Are all unital simple
C*-algebras K1-injective?" with no nuclearity clause.  If that quotation is
exact we are fine.  If the printed problem is posed inside the nuclear class,
then our `ProblemLIX` is a *weaker* universal and refuting it is *weaker* than
answering the printed question — the one direction in which this kind of
omission is not safe.  I cannot check a quotation against arXiv:2506.10902 from
here.  Mitigation, unformalised: the counterexample is an AH limit — corners of
matrix algebras over `C(X)` — hence nuclear in fact, so the mathematics would
survive the stricter reading; but nuclearity is nowhere proved in Lean, so the
repository could not today state the stronger form.  **A human should check the
quotation.**

## 5. The generic pieces

* `RelativeSupport.relPullback_eq_of_homotopy_of_line` — as general as its name:
  any contractible parameter space, any pairs, any positive degree, with the
  line hypothesis named in the name.  Its header already says what it is not
  (not homotopy invariance; mod-2 coefficients load-bearing).
* `Bundle.totalPiCohIso` — fully general in the bundle and the degree, no
  hypotheses beyond the bundle; header names the mechanism.  Cosmetic only: the
  docstring of `bijective_totalPiPull` opens a parenthesis after `piStar` and
  never closes it.
* `injective_relPullback_subInclusion` — see F4.
