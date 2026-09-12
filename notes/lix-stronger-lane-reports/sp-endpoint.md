# sp-endpoint

Owner of the endpoint: the assembly from the lanes' theorems to the stated theorem, and the
Palomar third configuration.  Program note `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.6;
statements drafted by `sp-design` under "Endpoint statements (for `sp-endpoint`)".

## GREEN (with job counts)

Two modules, two logs, on clone `xxii-fix`.  Two logs and not one because the two modules were
last changed at different times, and a green is for the bytes that were built: `ProblemLIXStrong`
changed after `SquarefreeDvd`'s green, so it has its own, and `SquarefreeDvd` is unchanged since
its own.

* **`GroupApproximation/Manuscript/NinetyNineProblems/ProblemLIXStrong.lean`** — PROBE GREEN,
  **8,705 jobs**, `EXIT=0`, log `.lake/laneprobe-20260910-155925.log`.  This is the probe AFTER
  `sp-design`'s spectral-pair ruling, so it is the green for the file as it stands.  Its
  artifacts were deleted first, so:

  ```
  ℹ [8705/8705] Built GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong (285s)
  ```

  Thirteen `#audit_axioms` reports, every one `[propext, Classical.choice, Quot.sound]`; zero
  `sorryAx` and zero `ofReduce*` in the log.  Purge 0 of 50 oleans.  `SquarefreeDvd` appears in
  this log as `Replayed`, not silent, which is what an unchanged import should read as.
* **`GroupApproximation/Manuscript/NinetyNineProblems/SquarefreeDvd.lean`** — PROBE GREEN,
  8,705 jobs, `EXIT=0`, log `.lake/laneprobe-20260910-154737.log`, artifacts deleted first:

  ```
  ℹ [4503/4533] Built GroupApproximation.Manuscript.NinetyNineProblems.SquarefreeDvd (55s)
  ```

  Three `#audit_axioms` reports, all three classical axioms.  Unchanged since, and untouched by
  the spectral-pair switch, which is why that log is still the right one to cite for it.

  Both modules are LEAF modules and both were named explicitly on every probe command, per
  `sp-tower`'s 13:20 rule that a closure gate is blind to a leaf.

  Three greens were produced at 8,705 jobs today and only the last one counts for
  `ProblemLIXStrong`.  Two were superseded by later edits to that file — one a docstring pass,
  one the instance switch.  That is the rule working rather than failing: greens on three byte
  sequences are not cumulative evidence for the third, and a docstring-only edit is not an
  exception, because the cheap way to be sure an edit was docstring-only is to re-probe.
* **`scripts/check_palomar_submission.py`** — `--self-test` passes: clean tree no findings, 15
  planted defects each reported (11 before, plus the four new ones for the third surface), 3
  YAML calibrations skipped locally because this interpreter has no PyYAML (CI installs it).
  The plain run is clean on the real tree and exits 0.
* **`.github/workflows/palomar-check.yml`** and **`palomar-comparator.yml`** parse as YAML and
  the check workflow's step list is the intended one (three axiom-closure steps and one verdict
  step that requires all three).  `lakefile.toml` parses and `defaultTargets` is unchanged.

## AUTHORED, UNVERIFIED

Four files and five gate edits, none of them built.  `laneprobe.sh` cannot build anything
outside `GroupApproximation/`, so the two Palomar modules and the three drivers need the lead
(see NEEDS); the shell script and the two workflows have been checked as text and as YAML only.

* `Palomar/LIXStrongChallenge.lean` — 192 lines, 9,918 bytes (hard caps 1,000 lines / 100 KiB;
  preferred 300 / 32 KiB, so it is inside the preferred budget).  Namespace `ProblemLIXStrong`,
  the three statements as `sp-design` drafted them, `sorry` bodies.
* `Palomar/comparator-lix-strong.json` — the third configuration, four keys, the three
  classical axioms.
* `Palomar/LIXStrongSolution.lean` — 185 lines, sorry-free.  One bridge (`powers_witness_of`)
  and the three statements under names ending `_of`, each carrying the one outstanding
  proposition.
* `scripts/PalomarLIXStrongChallengeType.lean`, `scripts/PalomarLIXStrongSolutionType.lean`,
  `scripts/PalomarLIXStrongAxioms.lean`.
* `lakefile.toml` — two new `lean_lib` entries, deliberately NOT in `defaultTargets`.
* `scripts/check_palomar_statement_match.sh`, `.github/workflows/palomar-check.yml`,
  `.github/workflows/palomar-comparator.yml`.

### The shape of the interim state, and why the gates say so

The three challenge theorems have no hypotheses and cannot be proved today.  So the solution
proves each of them from one named proposition,
`GroupApproximation.NinetyNineProblems.ClimbedPowersOutside n`, under the name with `_of`
appended.  Consequences, all deliberate and all recorded in the gates themselves:

* `Palomar/comparator-lix-strong.json` is in a new `PALOMAR_PENDING_CONFIGS` list, not in
  `PALOMAR_CONFIGS`.  A pending configuration gets every check that is meaningful now — the
  JSON's shape and keys, the challenge importing Mathlib alone, the size caps, the modules
  resolving to real files, the shared block matching between its own two files — and is
  excluded from exactly two rules: the challenge-versus-solution signature comparison, and the
  `formalization.yaml` requirement that every selected theorem appear in `status.main_results`.
* It is **not** excluded from the axiom-closure check.  The `_of` forms are sorry-free, so
  their closure is already the closure the finished theorems will have; a `sorryAx` reaching
  them through the development is a real defect today.  `scripts/PalomarLIXStrongAxioms.lean`
  gates in full, and `palomar-check.yml`'s verdict step now requires all three drivers.
* The statement-match script gates the pending pair on the **shared block only**.  The two
  strengthened drivers print `cornerDiag` and `IsK1Injective` first, then a line
  `pending-boundary:`, then the statements; the script diffs everything before the boundary and
  fails on a difference, and prints the rest without gating.  That is not a token check: an
  elaboration difference in `cornerDiag` fails the real Comparator, because `cornerDiag` is in
  the compared closure of all three theorems, and it is the exact shape of the defect that hit
  this repository at 03:30 this morning.
* The distinction the script draws is between a diff that cannot hold yet and a driver that did
  not run.  A missing driver, a driver that fails, a report with no `declaration:` section, and
  a report with nothing before the boundary are all errors for the pending pair exactly as for
  the other two.
* Neither Palomar library is a `defaultTarget`.  Every lane in this shared checkout runs `lake
  build`, and a surface that is deliberately incomplete should not be on that path.  Both join
  when the missing proposition lands.

### Decisions taken, with their reasons

* **The shared block is byte-identical across all four Palomar files**, verified by comparing
  the `BEGIN`/`END` spans programmatically, not by eye.  It carries `IsK1Injective` into files
  where **no statement uses it**.  Ratified twice (program note §1.6, `sp-design`'s report);
  the reason is diffability, and the challenge docstring says so and says that
  `¬ IsK1Injective A` follows from the power clause at `k = 1` with the stabilisation clause,
  so the unused definition is not an unexplained one.  Dropping it from the strong pair is a
  one-line change if the lead prefers.
* **The shared block I copied is the WORKING-TREE version, not the committed one.**
  `Palomar/LIXChallenge.lean` and `Palomar/LIXSolution.lean` are both dirty in the shared tree,
  written in the same second at 11:43:57 by someone else's prose pass (the `BEGIN SHARED BLOCK`
  marker now names both files, and `cornerDiag`'s docstring lost its last sentence).  I did not
  touch either file and will not.  I copied from what is on disk, and all four blocks are
  byte-identical as things stand.  If that prose pass is reverted or changed before it lands,
  the two strengthened files' blocks diverge from the other two and must be re-copied — the
  gate reports it, but only as a divergence within each pair, not across pairs.
* **`Nontrivial A` is kept as a conjunct** although Mathlib's `IsSimpleRing` extends
  `IsSimpleOrder` extends `Nontrivial`.  The printed problem names nontriviality and a reader
  should not have to know the implication.  `sp-design`'s draft; the existing `n = 2` surface
  omits it.
* **`v ∉ U₀(A)` is not a conjunct.**  It is the power clause at `k = 1`; the arithmetic is
  `not_forall_prime_dvd_one` and the C⋆-side reading is
  `hasK1InjWitness_of_hasK1InjPowerWitness`.
* **The spectral-order pair re-registered in `ProblemLIXStrong.lean` is
  `GroupApproximation.LIX.instSpectralPartialOrder`, at priority 100000 — REVERSED after
  `sp-design`'s ruling, and they were right.**  There are two such pairs in the tree: the
  `GroupApproximation` one in `Analysis/LIXEndpointStatement.lean`, which is where
  `HasK1InjWitness` is stated and whose docstring tells a consumer to reuse it; and the
  `GroupApproximation.LIX` one in `Analysis/LIXLimitMatrixTransport.lean`, which all eight
  rank-`n` files under `Analysis/` register.  I first picked the `GroupApproximation` pair,
  reasoning that `HasK1InjPowerWitness` must imply `HasK1InjWitness` on the nose.  That
  reasoning is sound and about the wrong end of the arrow: consuming a `def` needs only
  definitional equality, which `exact` supplies under either pair, because the `def`'s body was
  fixed when it was elaborated.  The binding consideration is the PRODUCER.
  `ClimbedPowersOutside` is a statement `sp-tower` has to prove, in files that register the LIX
  pair, and a proof that `rw`s or `simp`s against it needs the instances to match syntactically.
  Match the producer's spelling.  The Palomar files are immune either way: they write
  `letI : PartialOrder A := CStarAlgebra.spectralOrder A` inline and name neither pair, as the
  existing surface does.  `sp-design` has flagged the duplicate to the lead as a tree hazard in
  its own right; it is exactly the "fresh pair, definitionally equal but not the same term" that
  `LIXEndpointStatement`'s own docstring forbids.
* **`Squarefree N` is the one new instance-resolution surface** the third configuration adds.
  It is `@Squarefree ℕ inst N`, and at the pin the only `Monoid ℕ` instances are
  `Nat.instCommMonoid` and the shortcut `Nat.instMonoid`, both in
  `Mathlib/Algebra/Group/Nat/Defs.lean`, which every environment imports — so unlike this
  morning's `Fintype (Fin 2)`, the development cannot reach a third one.  The statement-match
  driver decides it.  If it does differ, the fallback with no instance at all is
  `∀ p : ℕ, p.Prime → ¬ p * p ∣ N` (`Nat.squarefree_iff_prime_squarefree`).
* **Binder names are part of the compared type.**  `hash info.type` hashes an `Expr` whose
  `forallE` nodes carry the binder name, and the drivers print the type under `pp.all`.  So the
  challenge's `(n : ℕ) (hn : 2 ≤ n)` and `(N : ℕ) (hN : 2 ≤ N) (hsq : Squarefree N)` must be
  spelled identically in the solution, names included.  Renaming `hn` to `_hn` in the challenge
  to silence the unused-variable linter would fail the statement match, so the challenge keeps
  the warning; it has three `sorry` warnings already and the library has no
  `warningAsError`.
* **`six_dvd_of_forall_prime_dvd` is proved from coprimality, not as an instance of the
  squarefree lemma**, so that the headline instance rests on no decision procedure for
  `Squarefree 6`.
* **`formalization.yaml` is NOT edited.**  A `status.main_results` row carries `sorry_count`
  and an axiom list, and the alignment rows carry `status: proved`; adding rows for theorems
  whose solution still takes a hypothesis would publish a false claim in the file the registry
  reads.  The rows are drafted below and are applied in the same change that moves the
  configuration out of the pending list.

## NEEDS

1. **A Palomar build, from the lead.**  `laneprobe.sh` syncs only `GroupApproximation/`, so it
   cannot build a `Palomar.*` target at all (FLEET_TRAPS 112).  The asks, in order, on the main
   tree:

   ```
   lake build PalomarLIXStrongChallenge
   lake build PalomarLIXStrongSolution
   lake env lean scripts/PalomarLIXStrongChallengeType.lean
   lake env lean scripts/PalomarLIXStrongSolutionType.lean
   lake env lean scripts/PalomarLIXStrongAxioms.lean
   bash scripts/check_palomar_statement_match.sh
   ```

   The first is cheap: the challenge imports Mathlib only.  The rest need the development.
2. **`sp-tower`** (message sent, awaiting reply): the names of the `k`-indexed Corollary-4
   chain, and whether they will publish the witness at the LIMIT or stage-wise.  The endpoint
   needs ONE fixed `v` satisfying both clauses; a proposition that re-quantifies the unitary per
   exponent bounds no order and I will not state one.  `ClimbedPowersOutside n` is the shape I
   have committed to; if `sp-tower` wants a different one, it is a rename in two files.
3. **`sp-design` — ANSWERED, both rulings applied.**  The topological input carries no prime:
   `p` appears nowhere in `¬ ContinuousMvNEquiv FHmat_k EHmat`, and enters only in the discharge
   (Step C needs `p ∤ k`, Step D needs `p ∣ n`).  Their `LemmaTwoHoldsPow n k` is exactly my
   `LemmaTwoHoldsForSections n (b k)` at the family `fun m => Σψ_k (bVec n m)`, so the two
   vocabularies agree and the existential over `p` sits in the witness theorem's hypothesis,
   where it is used, rather than in the named `Prop`.  They also caught a composition-order slip
   in my docstring — the suspension applies to the SPHERE VECTOR `bVec n m`, not to the base
   point `m`, since `b = x ∘ Σψ_k` means `b m = Σψ_k (x m)` — which is the same slip shape as
   the programme note's §1.3.2 correction.  Fixed.  `norm_suspPsi`, the lemma that the composed
   section still has unit norm so the zero-locus lemma fires, is `sp-powers`' and `sp-tower`'s,
   beside their definition of the family.
4. **A ruling from the lead on the pending tier**, if the two-list design is not wanted.  The
   alternative is to leave the third configuration out of the gates entirely until it closes,
   which leaves the challenge, the JSON and the two modules checked by nothing.

## Proposed root wiring (not applied — `GroupApproximation.lean` is the lead's)

Two lines, next to the other `NinetyNineProblems` imports (the block at lines 2159-2165):

```lean
import GroupApproximation.Manuscript.NinetyNineProblems.SquarefreeDvd
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong
```

The second imports the first, so the first is redundant for the build and is proposed anyway:
the root file is the tree's inventory, and a module reachable only through another is invisible
in it.  Land them together or not at all — `ProblemLIXStrong` without `SquarefreeDvd` on disk is
a dangling import, and `SquarefreeDvd` alone is a leaf nothing exercises.

## Proposed `formalization.yaml` rows (not applied — see the decision above)

To be added under `status.main_results` on the day `ClimbedPowersOutside` becomes a theorem,
with the axiom lists taken from a completed `PalomarLIXStrongAxioms` run and never from a guess:

```yaml
    - declaration: ProblemLIXStrong.exists_simple_separable_powers_outside_U0
      file: Palomar/LIXStrongSolution.lean
      sorry_count: 0
      axioms: [propext, Classical.choice, Quot.sound]
      comparator_config: Palomar/comparator-lix-strong.json

    - declaration: ProblemLIXStrong.exists_simple_separable_order_six_witness
      file: Palomar/LIXStrongSolution.lean
      sorry_count: 0
      axioms: [propext, Classical.choice, Quot.sound]
      comparator_config: Palomar/comparator-lix-strong.json

    - declaration: ProblemLIXStrong.exists_simple_separable_squarefree_witness
      file: Palomar/LIXStrongSolution.lean
      sorry_count: 0
      axioms: [propext, Classical.choice, Quot.sound]
      comparator_config: Palomar/comparator-lix-strong.json
```

and under `alignment.statements`:

```yaml
    - source: >-
        Problem LIX, strengthened: for every n >= 2 there is a separable simple
        unital C*-algebra with a unitary whose class dies at the first
        stabilisation and whose powers leave U0(A) unless the exponent is
        divisible by every prime dividing n.
      lean: ProblemLIXStrong.exists_simple_separable_powers_outside_U0
      module: Palomar.LIXStrongChallenge
      status: proved

    - source: >-
        The n = 6 instance: an element of U(A)/U0(A) of order divisible by six,
        or of infinite order, that is trivial in K1.
      lean: ProblemLIXStrong.exists_simple_separable_order_six_witness
      module: Palomar.LIXStrongChallenge
      status: proved

    - source: >-
        Every squarefree order: for squarefree N >= 2 an element of U(A)/U0(A)
        whose order is divisible by N, trivial in K1.
      lean: ProblemLIXStrong.exists_simple_separable_squarefree_witness
      module: Palomar.LIXStrongChallenge
      status: proved
```

`project.name`, `project.description` and `fidelity.divergences` also need a sentence each when
the third surface is submitted; the divergence to add is that the order of the witness class is
bounded below and never computed, and that `p²` is outside what the method sees.

## Proposed Cairn node text (not applied — `research/stw99-problem-lix-simple-k1-injective.md`)

To be appended after the existing "Palomar submission surface (2026-09-10)" paragraph, and only
once the proposition is discharged; while it is outstanding the accurate version is the second
paragraph alone.

> **Strengthened surface (2026-09-10).** A third Comparator configuration,
> `Palomar/comparator-lix-strong.json`, offers the same counterexample with the order of the
> witness class bounded below. For every n >= 2 the rank-n tower gives a separable simple unital
> C\*-algebra with a unitary v whose stabilisation diag(v, 1) is null-homotopic in U(M2(A)) and
> whose powers leave U0(A) unless the exponent is divisible by every prime dividing n; at n = 6
> that is an element of U(A)/U0(A) of order divisible by six, or of infinite order, trivial in
> K1, and for squarefree N it is order divisible by N. The bound is a divisibility and not an
> order: mod-p cohomology sees p and not p^2, so the sharp statement this method yields is
> divisibility by the radical of n, which is n exactly when n is squarefree. Nothing here
> computes K1(A), the exact order of v, or the component group; the integral statements of
> `stw59-simple-ah-factorial-unitary-torsion` remain unformalized and rest on Bott's
> pi_{2n}(U(n)) = Z/n!, which is not available without literature input.
>
> Not yet submitted: `Palomar/LIXStrongSolution.lean` proves the three statements from one
> proposition of the construction, the k-indexed Corollary 4 at the limit, and the configuration
> is listed as pending in `scripts/check_palomar_submission.py` until that proposition is a
> theorem.

## TRAPS

* (sp-endpoint, 09-10) `laneprobe.sh` cannot probe the Palomar surface at all — it rsyncs only
  `GroupApproximation/` and `GroupApproximation.lean`, so nothing under `Palomar/` or
  `scripts/` ever reaches the clone and the target does not exist there.  Recorded by `sp-tower`
  as FLEET_TRAPS 112 for `Palomar.LIXSolution`; it applies to every file outside
  `GroupApproximation/`, which for this lane is most of the deliverables.
* (sp-endpoint, 09-10) A compared theorem's BINDER NAMES are part of what
  `scripts/PalomarLIX*Type.lean` compares: `hash info.type` hashes an `Expr` whose `forallE`
  nodes carry the name, and the same driver prints the type under `pp.all`.  The existing `n = 2`
  surface never noticed because none of its three theorems takes an argument; all three of the
  stronger ones do.  So a binder renamed on one side to silence a linter is a statement
  mismatch.
* (sp-endpoint, 09-10) `sed -n '/start/,/end/p'` RESTARTS its range when the opening address
  matches again after the closing one has fired.  My first cut at "the report up to the first
  `pending-boundary:` line" used one, and on a report with several `declaration:` sections it
  returned every section, boundary or no boundary — so the gate would have compared exactly the
  sections it exists not to compare, and reported a difference that is the expected state of the
  work.  Replaced by `awk '/^pending-boundary:/{found=1; exit} {print} END{if(!found) exit 3}'`,
  which stops at the first boundary and FAILS when there is none.  Caught by running the
  extraction on a synthetic three-section report, not by reading it.
* (sp-endpoint, 09-10) `#audit_closed_axioms` rejects a theorem with ANY leading input, a
  hypothesis included, and its message is about "construction data", which reads as though the
  objection were to a `def` argument.  Three pure-`ℕ` lemmas taking `Squarefree N` and a
  universally quantified hypothesis failed a whole probe on it.  The rule is mechanical: the
  closed gate is for statements with no arguments at all; everything else takes `#audit_axioms`.
  The Lean itself elaborated fine in that run, so the failure looked like a proof error and was
  not one.
