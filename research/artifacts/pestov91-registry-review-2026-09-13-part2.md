# Pestov Open Question 9.1: simulated Palomar registry review, 2026-09-13 (part 2 of 2)

Lane `pc-registry`, 02:45–03:10 CDT.  Part 1, `pestov91-registry-review-2026-09-13.md`, holds the 43-item
checklist and its grades at `3e9636d74`.  This part records:
- each landing on the Pestov 9.1 surface, reviewed against that checklist;
- the state of the `Palomar check` workflow;
- the findings sent to lanes;
- the readiness verdict.

**Ownership.**
- The Palomar pair on main, its configuration, its pending registration, its drivers and its model tests were landed
  by session 6dbfc571's fz swarm: lanes p91-palomar, fz-integrate and p91-statement.
- That swarm also owns the yaml rows, the root imports and the Comparator run.
- This lane cannot message it, so findings on its files went to the PC lanes editing the same files (pc-palomar,
  pc-integrate), and this record is the channel to the owners.

## 1. Landings reviewed

### 1.1 `257b50a5d`: `wip/pestov91/fidelity/Pestov91ModelTests.lean` (p91-statement)

Checklist item E3, definition fidelity.
- **Page locators.** All nine match the arXiv v8 PDF as extracted here (§0 of part 1): Example 2.3 p. 5, Example 2.7
  p. 6, Definitions 3.1–3.2 p. 6, Theorem 3.3 p. 7, Theorem 3.5 p. 8, Theorem 3.6 and Remark 3.7 p. 9, Open question
  9.1 p. 21.
- **`PestovSoficModel`** renders Theorem 3.5 (1) and (3).
  - Multiplicativity is asked only when g, h, gh ∈ F; separation is 1/4.
  - The map is defined on all of G. A map on F extends arbitrarily, so nothing changes.
  - `≤ ε` in place of `< ε` is immaterial, since ε ranges over all positive reals.
  - Condition (2) is `test_identity_clause_is_implied`.
  - `isSoficGroup_iff_isPestovSofic` is a genuine equivalence.
- **`PestovHyperlinearModel`** renders Theorem 3.6 (1) and (3) with `‖·‖₂ = √hsDistSq`, which checks the squaring
  convention.
  - Only one direction is proved, `isPestovHyperlinear_of_isHyperlinearGroup`, and condition (2) is left out.
  - The docstring discloses both.
  - For an existential theorem the proved direction is the one that matters: the block's notion implies Pestov's.
  - Condition (2) follows from left invariance of the normalized Hilbert–Schmidt norm under unitaries
    (‖UA‖₂ = ‖A‖₂), which is not formalized.
- **Negative controls, each conjunct load-bearing.**
  - ℤ has no Kazhdan pair; a nonpositive tolerance is refused.
  - PUnit is not simple.
  - ℤ/2 meets every conjunct except `Infinite`.
  - ℤ meets every conjunct except property (T).
- **Evidence.** Probe 0913-021315-6428, as the commit message reports it: 22 closures, all within the permitted three;
  `test_not_isSimpleGroup_punit` uses [propext, Quot.sound]. The file is unwired, so that record is the only evidence,
  and a `review.notes` pointer to the file counts only once resolved at the submitted commit.
- **Grade.** E3 stays ADVISORY and positive.
  - The yaml fidelity paragraph may cite `isSoficGroup_iff_isPestovSofic` as an equivalence.
  - It must describe hyperlinearity as an implication to conditions (1) and (3), with (2) by unitary invariance.
  - It must not claim an equivalence for hyperlinearity.

### 1.2 `764023101`: pending registration of the pair (fz-integrate)

Graded in part 1 (C1–C4 PASS, B2 PASS). One defect, B1.
- The two type drivers seed the closure walk of each shared definition from its type alone.
- So the gated pre-boundary section never compares the definitions' bodies, which is where an instance captured
  differently makes the real Comparator fail.
- `scripts/PalomarBowenChapmanChallengeType.lean` seeds the walk from the value.
- Sent to pc-palomar, which is rewriting those drivers' target lists (§3).

### 1.3 `b78e01714`: `attic/.../ugc.O` → `ugc.O.txt` (pc-integrate)

Here is why `Palomar check` has been red since 06:49Z.
- Runs 34743705887 (06:49Z, head 398373fe3) and 34745087732 (07:23Z, head 764023101) have identical gate output, read
  from their logs.
  - The self-test is green (23, then 31, planted defects each reported; the clean copy has no findings).
  - The real run has exactly one finding: `attic/gottschalk-swarm-2026-09-12/sweep/ugc.O is a compiled artifact and is
    tracked` (`palomar: 1 finding(s)`).
  - Every later step was skipped.
  - The six axiom-closure "failure" lines are downstream, since no Lean was built.
- After b78e01714 no tracked path at main's tip has a suffix the gate treats as compiled output (`.a .bc .dll .dylib
  .ilean .ir .o .obj .olean .so .trace`, `.olean.private`, `.olean.server`). So the gate's only finding is gone.
- **Confirmed by CI for the gate step.** b78e01714 touches only `attic/`, outside the workflow's path filter.
  - The first run on a commit containing it is 34746055734, head 4a9981630, triggered by the yaml landing of §1.4.
  - Its step "Calibrate and run the submission gate" completed with **success** (02:47 CDT).
  - The same run is the first since 06:49Z to reach the build, the statement match and the six axiom drivers,
    including the Pestov 9.1 pending drivers. Those steps were still running when this part was landed.
- This lane dispatched nothing.

### 1.4 `4a9981630`: Pestov 9.1 literature rows in `formalization.yaml` (PC swarm, from pc-lit-background's rows)

15 rows added and 3 extended. No project, status, automation, review, fidelity or alignment field was touched, which
is the sequencing rule of the gaps file (§0). Origin shape: 2 original-proof rows, 0 substantive relationships (A7
holds).
- **F1 PASS.** The Pestov row has `location: Theorem 3.5 and Open question 9.1` and quotes the question verbatim, as
  the question "checked by", not "answered by", `Palomar/comparator-pestov91.json`. That is true while the Solution
  holds `_of` forms.
  - "The challenge's IsSoficGroup and IsHyperlinearGroup imply these two criteria" is true mathematically.
  - In Lean, only Theorem 3.5 in full and Theorem 3.6 (1) and (3) are derived (§1.1). The note claims nothing about
    Lean.
- **F2 PASS.** Ozawa 2004, `location: Section 7, after Theorem 7.4`, with the sentence Pestov cites as [64].
- **F3 PASS.** Ershov–Jaikin-Zapirain: the note now covers both witnesses, and records the earlier commutative and
  stable-range cases.
- **F4 partial.** Brown–Clark–Farthing–Sims Theorem 4.1 (over ℂ), Clark–Edie-Michell Corollary 4.6 and Steinberg
  Corollary 3.6 (over a field) are added. The Clark–Edie-Michell note names only what is on main
  (`isSimpleRing_of_minimal_free`).
  - Grigorchuk–Medynets is held back until the ring-level LEF module lands, because its note would claim Lean that is
    not on main.
  - That is the right restraint, and F4 closes with that row.
- **F5 PASS.**
  - Thom 0810.2180 Theorem 1.4 (not simple), and Kirchberg 1994 (F) + (T) ⇒ RF.
  - Caprace–Rémy and Gromov 1987, the known sources of simple Kazhdan groups.
  - Pestov–Kwiatkowska (arXiv v4 p. 28: "it remains in particular unknown whether finitely generated simple Kazhdan
    groups can be hyperlinear/sofic").
  - Alekseev–Thom (Section 5, Open problem 6.1), Cornulier 2011, Capraro–Lupini.
- **F6 PASS.** Dadarlat, Proposition 3.19, quotes "It is clear from definitions that MF ⇒ weak quasidiagonality", and
  says the witness shows the clause fails for groups. It discloses that the consequence is not formalized and that
  the journal text was not compared.
- **F7 GAP.** The search bound belongs in the original-proof row, which has not landed.
- **Internal notes only, no finding.**
  - The Caprace–Rémy row uses "a finitely presented LEF group is residually finite" without a source. It is a
    standard fact and not a material claim.
  - The Vershik–Gordon row has no `id` and was not read, and its note claims nothing from it.
  - Pestov–Kwiatkowska phrase the open question for finitely generated groups. A discrete Kazhdan group is finitely
    generated (Bekka–de la Harpe–Valette, Theorem 1.3.1), so the witness meets that form too, with no extra claim
    needed.

## 2. Drafts in flight (not on main at `4a9981630`)

- **pc-palomar.**
  - A third compared theorem, `Pestov91.exists_infinite_simple_propertyT_sofic_hyperlinear`.
  - The rename `hsDistSq` → `hilbertSchmidtDistSq`, and the definitions reordered.
  - The drafts' configuration, Challenge, Solution and probe driver agree on the three names (checked at 02:19).
  - A landing must carry the matching drivers, the gate's `_of` planter and the yaml rows (part 1 C2, D2).
- **pc-assembly.** `GroupApproximation/Pestov91/EndpointOfLeaves.lean`: four conditional theorems, and its docstring
  says they are conditional. The hypothesis-free endpoint is not drafted yet.
- **pc-integrate.** yaml rows and a README section, with FILL markers for credit, sources and fidelity. The concrete
  edits requested of this lane are in `$PC/lanes/pc-registry/pestov91-registry-gaps.md` (not a repository file):
  - the header;
  - classification: no MSC swap, `math.RA` optional;
  - a third original-proof row, with the origin constraints;
  - the infinitely presented witness;
  - predicted literature findings: the Dadarlat arrow, the search bound, the Pestov and Ozawa rows, the mechanism
    sources, the nearest earlier objects;
  - scope, main_results, alignment, fidelity, automation and review rows, and the README.

## 3. Findings sent

| to | finding | state |
|---|---|---|
| pc-palomar | the Challenge sentence "increasing exhaustion" assumes a countable group; Pestov's proof of Theorem 3.5 indexes by pairs (F, 1/n) | open |
| pc-palomar | the pending type drivers never hash the shared definitions' values (B1) | open |
| pc-palomar | "no statement-match or axiom driver on main" | **withdrawn**: it was false when sent, since 764023101 had landed |
| pc-integrate | nine of twelve Pestov91 modules are outside the root import closure; the root imports `RingFinitelyGenerated`, which reaches `CrossedProductFG` and `CrossedProduct` (C5) | open |
| pc-integrate | classification: no MSC change; `math.RA` optional (D8) | answered |
| pc-integrate | the draft proof account describes towers of cylinders, but main proves simplicity by split-annihilator root detection (`SplitSimplicity.lean`) (G5) | open |
| pc-integrate | the gaps file of §2 | delivered |

Findings withdrawn during review, before any message was sent:
- a config/Challenge name mismatch (P1), fixed in pc-palomar's 02:19 drafts;
- the dropped universe justification (P2), restored;
- "separation near the maximum" (P3), removed;
- a Solution header saying "proves" while conditional (P5), reverted to "derives".

## 4. Verdict at `4a9981630`

Checklist counts, regraded from part 1 with §1.4 applied:

| status | count | items |
|---|---|---|
| PASS | 22 | A1–A4, A6–A8, B2, C1–C4, F1–F3, F5–F6, G1–G4, G7 |
| GAP | 14 | B1, C5, D1–D3, D5–D7, E1–E2, F4, F7, G6, G8 |
| PENDING | 5 | A5, B3, B4, D4, G5 |
| ADVISORY | 2 | D8, E3 |

**Not ready.** Blocking, in the order a submission would hit them:
1. **A5 / D4 / B3.** The Solution has no hypothesis-free theorem, so no Comparator run and no `status.main_results`
   rows are possible. The endpoint is owed by pc-assembly.
2. **B1.** While the pair is pending, the local statement match cannot detect an instance captured inside the shared
   block. The final gate covers it once the statements are compared, but the renamed block will be landed against
   the blind gate.
3. **C5.** Nine Pestov91 modules are outside the root import closure, which the repository's Source scan reports.
4. **D1–D3, D5–D7, E1–E2, F4 (Grigorchuk–Medynets), F7, G6.** The literature rows landed (§1.4), but the header,
   scope, main_results, original-proof row, automation, review, fidelity and alignment rows and the README section
   are not on main.
5. **CI.** Run 34746055734 cleared the submission gate. Its build, statement-match and axiom-closure steps had not
   finished when this part was landed (§1.3).

**Not blocking.**
- Notability: no finding predicted.
- Classification: no change required.
- The Challenge itself: Mathlib only, 149 lines, the question verbatim, the definitions model-tested.

**Predicted editorial outcome if submitted with every GAP closed as specified:** `neutral`.

The two residual risks are the literature account (F6, F7) and the proof account (G5). Both are presentation items,
correctable by the edits in §2.
