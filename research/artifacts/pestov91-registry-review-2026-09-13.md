# Pestov Open Question 9.1: simulated Palomar registry review, 2026-09-13 (part 1 of 2)

Lane `pc-registry` of the PC swarm, 02:00–02:45 CDT.  Part 1 fixes every requirement a Pestov 9.1 Comparator
configuration must meet and grades main against them.  Part 2, `pestov91-registry-review-2026-09-13-part2.md`,
grades the files landed by pc-palomar, pc-assembly and pc-integrate and gives the readiness verdict.

**Correction (02:45 CDT).** The first landing of this file (6965e0292) graded `e6b547260` and missed two commits
already on main:
- 257b50a5d, the model tests;
- 764023101, lane fz-integrate: the pending gate entry, the drivers, the lakefile libraries and the workflow steps.

Items B1–B3, C1–C5 and E3, and the table in §3, are regraded here at `3e9636d74`.

## 0. What was read

- **Policy.** These are copies fetched by lane bcx-registry on 2026-09-12 at 20:53 CDT from PalomarRegistry/PalomarPolicy
  and PalomarSubmission; they were not re-fetched here.
  - `CONTRIBUTING.md`: §1 (suitability), §2.2 (Challenge and Solution), §2.3 (Comparator configuration), §3.2
    (provenance), §3.3 (sources), §3.4 (informal account), §7 (editorial review).
  - `rubric.json` schema 10. The registry scores are `statement_alignment`, `definition_fidelity`, `notability`,
    `literature` and `clarity`. The minimum is 4 on each, and only notability is mandatory.
  - `prompts/00`–`04`, `prompts/materiality.md`, `taxonomies/classification-guide.md`.
- **Repository gates on main.**
  - `scripts/check_palomar_submission.py`;
  - `scripts/check_palomar_statement_match.sh`;
  - `scripts/PalomarPestov91{Axioms,ChallengeType,SolutionType}.lean`;
  - `.github/workflows/palomar-check.yml` and `palomar-comparator.yml`;
  - `tools/nm-swarm/palomar-verify.sh` and its remote template, which verify the LIX-strong surface only.
- **Precedent.**
  - `Palomar/BowenChapman{Challenge,Solution}.lean`, `Palomar/comparator-bowen-chapman.json`;
  - `scripts/PalomarBowenChapman{Axioms,ChallengeType,SolutionType}.lean`;
  - that submission's `formalization.yaml` rows;
  - `research/artifacts/bowen-chapman-problem-1-1-audit-2026-09-12.md` §9: defects D1–D12 of that simulated review,
    cited below as BC D*n*.
- **Primary source.** Pestov, arXiv:0804.3968v8 (pc-review's PDF, text extracted with `pdftotext`). Read: Definitions
  3.1–3.2, Theorems 3.5–3.6, Remark 3.7, the paragraph after it, and Section 9.

## 1. The question

PDF p. 21, verbatim:

> Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it be
> hyperlinear (sofic)?

The Challenge on main quotes this exactly, with the ligatures expanded.

## 2. Checklist

Status key:
- **PASS**: holds on main now.
- **GAP**: must change before submission.
- **PENDING**: cannot hold until the hypothesis-free endpoint lands.
- **ADVISORY**: not a registry defect.

Owners are in brackets. Inputs owed to pc-integrate come from pc-review, pc-priority-credit and pc-lit-background.

### A. Mechanical intake: failures here stop the submission before review

- **A1 PASS [pc-palomar].** The Challenge imports Mathlib only (§2.2; gate rule 3). Main has 7 Mathlib imports.
- **A2 PASS [pc-palomar].** Challenge size: the hard cap is 1,000 lines and 100 KiB, with a warning above 300 lines or
  32 KiB. Main's Challenge is 149 lines / 6,699 B.
- **A3 PASS [pc-palomar].** Distinct dotted module names resolving to regular files: `Palomar.Pestov91Challenge`,
  `Palomar.Pestov91Solution`.
- **A4 PASS [pc-palomar].** The config is one JSON object with exactly the four required keys, nonempty
  `theorem_names` and `permitted_axioms` = {propext, Quot.sound, Classical.choice} (§2.3).
- **A5 PENDING [pc-palomar, pc-assembly].** Every selected theorem must be declared in both modules. On main the
  Solution declares only `_of` forms, which take an infinite simple LEF group as a hypothesis.
- **A6 PASS [repository].** Toolchain v4.32.0 is at or above v4.28.0. There is one lakefile, the manifest pins full
  SHAs on github.com, and there is one Apache-2.0 `LICENSE`. There are no tracked artifacts, submodules or LFS.
- **A7 PASS [pc-integrate].** The sources satisfy exactly one origin alternative (§3.2).
  - A third `original-proof` row keeps `result_origin: original`.
  - Any `formalizes`, `adapts` or `independently-proves` row is a mechanical failure, not a finding.
- **A8 PASS [pc-integrate].** No AI system in `project.authors` or `responsible_maintainers`. They are `[Sauers]` and
  `[SauersML]`.

### B. The three Comparator verdicts

- **B1 GAP [pc-palomar].** Statement match. Comparator requires the compared types to be identical after
  elaboration, and every constant in their transitive closure to be identical in type and value. It rejected this
  repository twice on byte-identical source: an instance resolved differently in the challenge and the solution
  (non-MF, 2026-08-19; LIX, 2026-09-10).
  - The shared block is byte-identical on main (diffed here).
  - 764023101 added the two type drivers and put `Pestov91` in the pending loop of
    `check_palomar_statement_match.sh`, which gates on everything before `pending-boundary:`.
  - **The gated part is blind to the defect it is for.** For the six shared definitions, the walk is seeded from each
    definition's type only (`info.type.getUsedConstants`), and no hash of the definition's value is printed.
    - The type of `IsSoficGroup` is `(G : Type) → [Group G] → Prop`.
    - So the bodies are never compared: `hammingDist`, `Fintype.card`, the carrier instances, `Matrix.unitaryGroup Y ℂ`,
      `U g * U h`, the group on `E ≃ₗᵢ[ℂ] E`.
    - `scripts/PalomarBowenChapmanChallengeType.lean` seeds its walk from the value of each shared definition.
    - While the pair is pending, a captured instance inside the block passes this gate and fails the real Comparator.
      Once the pair is submittable, the statement section walks these values.
    - Sent to pc-palomar, which rewrites the drivers' target lists when it lands the renamed block.
- **B2 PASS [pc-palomar].** `scripts/PalomarPestov91Axioms.lean` (764023101) gates the axiom closure of both `_of`
  forms against the three permitted axioms, and logs an error on a missing name. Its list becomes the configuration's
  names when the configuration moves to `PALOMAR_CONFIGS`.
- **B3 PENDING [pc-integrate].** A real Comparator run with NanoDa on the submission commit must report "nanoda
  kernel accepts the solution / Lean default kernel accepts the solution / Your solution is okay!".
  - The run is `palomar-comparator.yml` with `config=Palomar/comparator-pestov91.json` and `nanoda=true`.
  - Since 764023101 the workflow builds both Pestov91 libraries.
  - The run waits for the endpoint.
- **B4 PENDING [pc-integrate].** Carry-over. A pass on commit P holds at a later commit S only if the Palomar import
  closure, toolchain, manifest, lakefile, configuration and workflow are byte-identical from P to S (BC audit §1).

### C. Repository gates

- **C1 PASS [pc-integrate].** `Palomar/comparator-pestov91.json` is in `PALOMAR_PENDING_CONFIGS` (764023101). It moves
  to `PALOMAR_CONFIGS` in the same change that adds the `status.main_results` rows.
- **C2 PASS [pc-integrate].** `SURFACE_FILES` lists the three paths, and four Pestov 9.1 calibrations exist: a
  project-local import, a one-sided shared-block edit, a missing `_of`, a fourth axiom. The metadata calibration
  arrives with the move to `PALOMAR_CONFIGS`. A rename of the `_of` theorems must also rename the planter's target
  string, or the self-test fails.
- **C3 PASS [pc-integrate].** `palomar-check.yml` has the Pestov91 driver paths, both libraries in the build step, an
  axiom-closure step and its reject variable.
- **C4 PASS [pc-integrate].** `lakefile.toml` has `PalomarPestov91Challenge` and `PalomarPestov91Solution`, outside
  `defaultTargets` while pending.
- **C5 GAP [pc-integrate].** At `3e9636d74`, `GroupApproximation.lean` has one Pestov91 import line for eleven files
  under `GroupApproximation/Pestov91/`. `scripts/check.py`'s `check_import_closure` reports every module outside the
  root closure. This is not a registry input, but it is a finding of the repository's own Source scan.

### D. `formalization.yaml`: statement alignment, clarity, provenance

- **D1 GAP [pc-integrate].** `project.description` does not mention the result. Prompt 02 makes it a finding when the
  abstract "omits a distinct principal result family represented by the selection" (BC D1).
- **D2 GAP [pc-integrate].** `project.name`, the default public entry title, names only the other two results
  (BC D6).
- **D3 GAP [pc-integrate].** `status.scope` must name both Pestov91 modules and say what they state (materiality;
  BC D2).
- **D4 PENDING [pc-integrate].** `status.main_results` needs one row per selected theorem, with
  `comparator_config: Palomar/comparator-pestov91.json`, `sorry_count: 0` and the axioms. Fill them only from a
  completed axiom run.
- **D5 GAP [pc-integrate ← pc-priority-credit].** A `type: original-proof`, `relationship: other` row titled for this
  result, with contributors and a first-presentation timeline in its note (§3.2; BC D4).
- **D6 GAP [pc-integrate ← pc-priority-credit].** `automation.methods` and `notes` must say who solved the problem and
  which systems wrote the Lean and the prose. "The two methods entries above" becomes three (prompt 01; BC D11).
- **D7 GAP [pc-integrate ← pc-review].** `review.notes` must point to a Pestov 9.1 review record that exists at the
  pinned commit (BC D12).
- **D8 ADVISORY.** The classification check is an egregious-mismatch screen only (prompt 00). `math.GR`, 20F65 and
  22D55 already describe the result, and MSC is at the cap of 8, so no change is required. `math.RA` may be added.

### E. Fidelity and alignment

- **E1 GAP [pc-integrate ← pc-review].** `alignment.statements` needs one row per selected theorem: the question in
  Pestov's words, `module: Palomar.Pestov91Challenge`, and `status: proved` only when proved.
- **E2 GAP [pc-integrate ← pc-review].** `fidelity.divergences` needs a Pestov 9.1 paragraph disclosing five points.
  1. Local finite-set forms stand in for Pestov's ultraproduct Definitions 3.1–3.2. Theorems 3.5–3.6 give the
     equivalence for an arbitrary group, and the paragraph after Remark 3.7 says "an apparent greater generality of
     allowing uncountable groups is an illusion".
  2. The shared forms ask for multiplicativity on all of F × F and separation 1 − ε in Hamming distance, or 2 − ε in
     squared normalized Hilbert–Schmidt distance. Theorems 3.5–3.6 ask it only when gh ∈ F, with an identity clause
     and separation 1/4; Remark 3.7 allows any constant up to √2. In an existential theorem, stronger conditions give
     a stronger theorem.
  3. Property (T) quantifies over complex Hilbert spaces in `Type` only. The restriction weakens the definition
     formally, and the orbit-span argument shows nothing is lost. The complex–real bridge is
     `hasKazhdanPropertyT_iff_complex`.
  4. For a discrete group the compact Kazhdan sets are the finite ones (Bekka–de la Harpe–Valette, Definition 1.1.3).
  5. Groups range over `Type 0`, and the witness is in `Type 0`.
- **E3 ADVISORY [pc-palomar].** Model tests. `wip/pestov91/fidelity/Pestov91ModelTests.lean` (257b50a5d) holds 22
  declarations in the Challenge vocabulary, with probe 0913-021315-6428 green.
  - Positive controls: finite groups and ℤ.
  - Negative controls: ℤ lacks (T), and PUnit is not simple.
  - `isSoficGroup_iff_isPestovSofic`, and `isPestovHyperlinear_of_isHyperlinearGroup` for Theorem 3.6 (1) and (3).
  - It is unwired, so its probe record is the only evidence. A `review.notes` pointer to it counts only once resolved
    at the pinned commit.

### F. Sources: literature

- **F1 GAP [pc-integrate ← pc-lit-background].** The Pestov 2008 row needs `location` Open question 9.1, p. 21, and the
  question verbatim. Its note today serves Bowen–Chapman alone.
- **F2 GAP.** Add Ozawa, *About the QWEP conjecture*, Internat. J. Math. 15 (2004), arXiv:math/0306067, which is
  Pestov's [64] and the origin of the question.
- **F3 GAP.** The Ershov–Jaikin-Zapirain row must also say that it gives the Pestov 9.1 witness property (T).
- **F4 GAP.** Rows for the mechanisms the Lean transfers or reproves, each `other` with what is reproved, or
  `background`:
  - Grigorchuk–Medynets, arXiv:1105.0719, Theorem 2.6;
  - Brown–Clark–Farthing–Sims, arXiv:1204.3127, Theorem 4.1;
  - Clark–Edie-Michell, arXiv:1403.4684, Corollary 4.6;
  - Steinberg, arXiv:1408.6014, Corollary 3.6;
  - Elek–Szabó.
- **F5 GAP.** The nearest earlier objects and the status of the question:
  - Thom, arXiv:0810.2180, Theorem 1.4, not simple, and Kirchberg's theorem, Theorem 1.1 there;
  - Caprace–Rémy and Gromov;
  - Pestov–Kwiatkowska, arXiv:0911.4266, still calling the question open.
- **F6 GAP.** Dadarlat, arXiv:2007.12655v2, introduction: "It is clear from definitions that MF ⇒ weak
  quasidiagonality".
  - With his remark (ii) that arrow makes every infinite simple Kazhdan group non-LEF, and the witness contradicts
    it (ex-novelty deep pass; writeup part 3 §8).
  - Leaving that out is the "omitted prior result … that changes the public account" of prompt 04.
- **F7 GAP [← pc-priority-credit].** Novelty must be stated with its search bound (§3.4).
  - The bound (writeup part 3 §10, the ex-novelty pass): 12 LaTeX sources grepped; citing works by title and abstract;
    Pisier 2020 and Arzhantseva 2014 unread.
  - The note claims no more than "within this bound, no earlier answer was found".

### G. Prose rules

- **G1 PASS [pc-palomar].** The Challenge docstring quotes the question verbatim, with a locator.
- **G2 PASS [pc-palomar].** Every shared definition has a docstring giving its ordinary meaning (§2.2).
- **G3 PASS [pc-palomar].** No prose says "proves" while the Solution is conditional. Main's Solution header says it
  "derives the statements … from any infinite simple LEF group of the development".
- **G4 PASS [pc-palomar].** Both modules carry "The prose of this module was written by Claude (Anthropic)."
- **G5 PENDING [pc-integrate].** An informal proof account in the README, the yaml or the Challenge docs triggers rubric
  step `proof_account`, which compares it with the Lean that is actually present (§3.4).
  - Simplicity of `EL₃(R)` on main is root detection with split annihilators (`Pestov91/SplitSimplicity.lean`), not
    towers of cylinders.
  - The witness subshift is period-doubling (blueprint D1), while writeup part 1 §2.4 uses Fibonacci.
- **G6 GAP [pc-integrate].** The README needs a section on the result (§3.4; BC D7).
- **G7 PASS.** No public text states, bounds or implies a registry score (§7).
- **G8 GAP [all].** The famous-problem clause (§1) requires a careful comparison with the question (E2), a serious
  literature account (F1–F7), and an honest statement of gaps (A5, D4, F7). A clear failure there is `rejected`.

## 3. State of main at `3e9636d74`

| status | count | items |
|---|---|---|
| PASS | 17 | A1–A4, A6–A8, B2, C1–C4, G1–G4, G7 |
| GAP | 19 | B1, C5, D1–D3, D5–D7, E1–E2, F1–F7, G6, G8 |
| PENDING | 5 | A5, B3, B4, D4, G5 |
| ADVISORY | 2 | D8, E3 |

**Not ready.** The Pestov 9.1 surface is gated as pending: drivers, gate entry, lakefile libraries and workflow steps
are on main. Four things remain:
- the Solution holds only `_of` forms, and the hypothesis-free endpoint is owed by pc-assembly;
- the pending statement-match gate does not compare the shared definitions' values (B1);
- the root carries one Pestov91 import line for eleven module files (C5);
- the metadata, sources, fidelity paragraph and README section are not written.

Expected editorial grading once the gaps close:
- Notability: the question is printed in Pestov's survey and originates with Ozawa, and the audience is operator
  algebras and approximation of groups. That fits the anchor "clear interest beyond a narrow specialist audience".
- The risks are F6 (the Dadarlat sentence) and F7 (the bounded search). Both are correctable presentation gaps.
