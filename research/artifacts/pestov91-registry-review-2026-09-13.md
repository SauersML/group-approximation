# Pestov Open Question 9.1: simulated Palomar registry review, 2026-09-13 (part 1 of 2)

Lane `pc-registry` of the PC swarm, 02:00–02:30 CDT.  Part 1 fixes every requirement a Pestov 9.1 Comparator
configuration must meet and grades main at `e6b547260` against them.  Part 2,
`pestov91-registry-review-2026-09-13-part2.md`, grades the files landed by pc-palomar, pc-assembly and pc-integrate
and gives the readiness verdict.

## 0. What was read

- **Policy.** These are copies fetched by lane bcx-registry on 2026-09-12 at 20:53 CDT from PalomarRegistry/PalomarPolicy
  and PalomarSubmission; they were not re-fetched here.
  - `CONTRIBUTING.md`: §1 (suitability), §2.2 (Challenge and Solution), §2.3 (Comparator configuration), §3.2
    (provenance), §3.3 (sources), §3.4 (informal account), §7 (editorial review).
  - `rubric.json` schema 10. The registry scores are `statement_alignment`, `definition_fidelity`, `notability`,
    `literature` and `clarity`. The minimum is 4 on each, and only notability is mandatory.
  - `prompts/00`–`04`, `prompts/materiality.md`, `taxonomies/classification-guide.md`.
- **Repository gates on main.**
  - `scripts/check_palomar_submission.py` (intake rules, shared block, signatures, metadata, self-test);
  - `scripts/check_palomar_statement_match.sh`;
  - `.github/workflows/palomar-check.yml` and `palomar-comparator.yml`;
  - `tools/nm-swarm/palomar-verify.sh` and its remote template, which verify the LIX-strong surface only and are no
    path for Pestov 9.1.
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

Owners are in brackets. Inputs owed to pc-integrate come from pc-review, pc-priority-credit and pc-lit-background, as
its FILL map says.

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
  SHAs on github.com, and there is one Apache-2.0 `LICENSE`. There are no tracked artifacts, submodules or LFS
  (§2.1, §2.4, §2.5). bcx-registry found these clean, and the gate re-checks them on every run.
- **A7 PASS [pc-integrate].** The sources satisfy exactly one origin alternative: every `original-proof` row is
  `other`, and no row is `formalizes`, `adapts` or `independently-proves` (§3.2).
  - A third `original-proof` row keeps `result_origin: original`.
  - Any substantive relationship on a Pestov 9.1 row is a mechanical failure, not a finding.
- **A8 PASS [pc-integrate].** No AI system in `project.authors` or `responsible_maintainers` (materiality). They are
  `[Sauers]` and `[SauersML]`.

### B. The three Comparator verdicts

- **B1 GAP [pc-palomar].** Statement match. Comparator requires the compared types to be identical after
  elaboration, and every constant in their transitive closure to be identical in type and value. It rejected this
  repository twice on byte-identical source: an instance resolved differently in the challenge and the solution
  (non-MF, 2026-08-19; LIX, 2026-09-10).
  - On main the shared block is byte-identical (diffed here), so the text check holds.
  - The elaborated check is absent: there are no `scripts/PalomarPestov91ChallengeType.lean` and
    `...SolutionType.lean`, and `check_palomar_statement_match.sh` loops only over the prefixes "", `LIX`,
    `BowenChapman` (plus pending `LIXStrong`).
  - Capture risks particular to this block: `Matrix.unitaryGroup Y ℂ`, the matrix product `U g * U h`, the
    decidability in `Finset.univ.filter`, the group structure on `E ≃ₗᵢ[ℂ] E`, and the coercion in `‖ρ q x - x‖`.
  - The drivers must walk the values of all six shared definitions, as the Bowen–Chapman drivers do.
- **B2 GAP [pc-palomar].** Axiom closure of each selected Solution theorem within the permitted three (§2.3). There is
  no `scripts/PalomarPestov91Axioms.lean` on main; b490bf08d records only a probe-only driver.
- **B3 GAP [pc-integrate].** A real Comparator run with NanoDa on the submission commit must report "nanoda kernel
  accepts the solution / Lean default kernel accepts the solution / Your solution is okay!".
  - The run is `palomar-comparator.yml` with `config=Palomar/comparator-pestov91.json` and `nanoda=true`.
  - Today its build step builds eight libraries, none of them Pestov 9.1, and `lakefile.toml` has no Pestov 9.1
    `lean_lib`.
- **B4 PENDING [pc-integrate].** Carry-over. A Comparator pass on commit P holds at a later commit S only if the
  Palomar import closure, toolchain, manifest, lakefile, configuration and workflow are byte-identical from P to S
  (BC audit §1, 428 files there).

### C. Repository gates

- **C1 GAP [pc-integrate].** `Palomar/comparator-pestov91.json` is in neither `PALOMAR_CONFIGS` nor
  `PALOMAR_PENDING_CONFIGS`.
  - While the Solution has only `_of` forms it belongs in the pending list, where the gate requires each `<name>_of`.
  - It moves to `PALOMAR_CONFIGS` in the same change that adds the `status.main_results` rows.
- **C2 GAP [pc-integrate].** `SURFACE_FILES` needs the three Pestov 9.1 paths. `CALIBRATION` needs Pestov 9.1
  planters: a project-local import, a one-sided shared-block edit, a one-sided signature edit (or a missing `_of`
  while pending), a fourth permitted axiom, and a result dropped from the metadata. Bowen–Chapman has five.
- **C3 GAP [pc-integrate].** `palomar-check.yml` needs the Pestov 9.1 drivers in the path filter, both libraries in
  the build step, an axiom-closure step, and that step in the final reject condition.
- **C4 GAP [pc-palomar, pc-integrate].** `lakefile.toml` needs `PalomarPestov91Challenge` and
  `PalomarPestov91Solution`. They join `defaultTargets` once the configuration is no longer pending.
- **C5 GAP [pc-integrate].** Eight modules sit at final paths with no import line in `GroupApproximation.lean`:
  Assembly, Centre, CentreSkew, Kazhdan, KazhdanUnitary, LEFHyperlinear, RingSimple and SplitSimplicity.
  - Each landing commit touched only its module.
  - `scripts/check.py`'s `check_import_closure` reports modules outside the root closure.
  - This is not a registry input, but it is a finding of the repository's own Source scan.

### D. `formalization.yaml`: statement alignment, clarity, provenance

- **D1 GAP [pc-integrate].** `project.description` does not mention the result. Prompt 02 makes it a finding when the
  abstract "omits a distinct principal result family represented by the selection" (BC D1).
- **D2 GAP [pc-integrate].** `project.name`, the default public entry title, names only the other two results
  (BC D6).
- **D3 GAP [pc-integrate].** `status.scope` must name `Palomar/Pestov91Challenge.lean` and
  `Palomar/Pestov91Solution.lean` and say what they state. Materiality: submission-specific prose must not misstate
  what the configuration contains (BC D2).
- **D4 PENDING [pc-integrate].** `status.main_results` needs one row per selected theorem, with
  `comparator_config: Palomar/comparator-pestov91.json`, `sorry_count: 0` and the axioms. Fill them only from a
  completed axiom run.
- **D5 GAP [pc-integrate ← pc-priority-credit].** A `type: original-proof`, `relationship: other` row titled for this
  result, with contributors and a first-presentation timeline in its note (§3.2; BC D4).
- **D6 GAP [pc-integrate ← pc-priority-credit].** `automation.methods` and `notes` must say who solved the problem and
  which systems wrote the Lean and the prose. "The two methods entries above" becomes three (prompt 01; BC D11).
- **D7 GAP [pc-integrate ← pc-review].** `review.notes` must point to a Pestov 9.1 review record that exists at the
  pinned commit (BC D12). A pointer counts only once resolved (materiality).
- **D8 ADVISORY.** The classification check is an egregious-mismatch screen only (prompt 00): a missing or better code
  is never a criticism.
  - `math.GR`, 20F65 and 22D55 already describe the result.
  - MSC is at the cap of 8, so no change is required.
  - `math.RA` may be added (5 of 8 arXiv classes).

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
  3. Property (T) quantifies over complex Hilbert spaces in `Type` only. Restricting the universe formally weakens
     the definition, and the orbit-span argument shows nothing is lost: the closed span of one orbit of a
     representation of a group in `Type` is isometric to a Hilbert space in `Type`. The development proves the
     complex–real bridge (`hasKazhdanPropertyT_iff_complex`).
  4. For a discrete group the compact Kazhdan sets are the finite ones (Bekka–de la Harpe–Valette, Definition 1.1.3).
  5. Groups range over `Type 0`, and the witness is in `Type 0`.
- **E3 ADVISORY [pc-palomar].** Model tests of the shared definitions in the pinned tree. A definition-fidelity score
  of 4 needs concrete positive evidence (§7).
  - Positive controls: finite groups have (T) and are sofic and hyperlinear.
  - Negative controls: ℤ lacks (T), and the trivial group is neither infinite nor simple.
  - None exist on main; pc-palomar's draft Solution has them.

### F. Sources: literature

- **F1 GAP [pc-integrate ← pc-lit-background].** The existing Pestov 2008 row needs `location` Open question 9.1,
  p. 21, and the question verbatim. Its note today serves Bowen–Chapman alone ("does not pose the converse").
- **F2 GAP.** Add Ozawa, *About the QWEP conjecture*, Internat. J. Math. 15 (2004), arXiv:math/0306067, which is
  Pestov's [64] and the origin of the question: "It is unknown whether there exists a simple property (T) group Γ
  which is hyperlinear".
- **F3 GAP.** The Ershov–Jaikin-Zapirain row (`other`) must also say that it gives the Pestov 9.1 witness property
  (T).
- **F4 GAP.** Rows for the mechanisms the Lean transfers or reproves, each `other` with what is reproved, or
  `background`, and never `adapts`:
  - Grigorchuk–Medynets, arXiv:1105.0719, Theorem 2.6;
  - Brown–Clark–Farthing–Sims, arXiv:1204.3127, Theorem 4.1;
  - Clark–Edie-Michell, arXiv:1403.4684, Corollary 4.6;
  - Steinberg, arXiv:1408.6014, Corollary 3.6;
  - Elek–Szabó, soficity implies hyperlinearity.
- **F5 GAP.** The nearest earlier objects and the status of the question:
  - Thom, arXiv:0810.2180, Theorem 1.4: a finitely generated LEF Kazhdan group, not simple. Kirchberg's theorem is
    Theorem 1.1 there.
  - Caprace–Rémy and Gromov, the two known sources of infinite simple Kazhdan groups.
  - Pestov–Kwiatkowska, arXiv:0911.4266, still calling the question open.
- **F6 GAP.** Dadarlat, arXiv:2007.12655v2, introduction: "It is clear from definitions that MF ⇒ weak
  quasidiagonality".
  - With his remark (ii), that arrow makes every infinite simple Kazhdan group non-MF, hence non-LEF, and the witness
    contradicts it. See the ex-novelty deep pass, "A tension to state explicitly", and writeup part 3 §8.
  - A printed statement the result contradicts is the "omitted prior result … that changes the public account" of
    prompt 04.
- **F7 GAP [← pc-priority-credit].** Novelty must be stated together with its search bound (§3.4: "Do not claim
  novelty without a credible literature search").
  - The bound, from writeup part 3 §10 and the ex-novelty pass: 12 LaTeX sources grepped; citing works of Ozawa,
    Pestov, Thom and six others by title and abstract; two surveys unread (Pisier 2020, Arzhantseva 2014).
  - The note must claim no more than "within this bound, no earlier answer was found".

### G. Prose rules

- **G1 PASS [pc-palomar].** The Challenge docstring quotes the question verbatim, with a locator.
- **G2 PASS [pc-palomar].** Every shared definition has a docstring giving its ordinary meaning (§2.2).
- **G3 PASS [pc-palomar].** No prose says "proves" while the Solution is conditional (the erdos501 warning shape). Main's
  Solution header says it "derives the statements … from any infinite simple LEF group of the development".
- **G4 PASS [pc-palomar].** Both modules carry "The prose of this module was written by Claude (Anthropic)." (BC
  batch 2).
- **G5 PENDING [pc-integrate].** Any informal proof account in the README, the yaml or the Challenge docs triggers
  rubric step `proof_account`, which compares it with the Lean that is actually present (§3.4).
  - The Lean witness uses the period-doubling Toeplitz subshift (blueprint D1).
  - `research/artifacts/pestov-9-1-writeup-2026-09-13-part1.md` §2.4 uses the Fibonacci subshift.
  - Any account a `review.notes` pointer reaches must say which one the Lean uses.
- **G6 GAP [pc-integrate].** The README needs a section on the result (§3.4; BC D7).
- **G7 PASS.** No public text states, bounds or implies a registry score (§7).
- **G8 GAP [all].** The famous-problem clause (§1) requires a careful comparison with the question (E2), a serious
  literature account (F1–F7), and an honest statement of gaps (A5, D4, F7). A clear failure there is `rejected`, not
  `revision_required`.

## 3. State of main at `e6b547260`

| status | count | items |
|---|---|---|
| PASS | 12 | A1–A4, A6–A8, G1–G4, G7 |
| GAP | 25 | B1–B3, C1–C5, D1–D3, D5–D7, E1–E2, F1–F7, G6, G8 |
| PENDING | 4 | A5, B4, D4, G5 |
| ADVISORY | 2 | D8, E3 |

**Not ready.** On main the Pestov 9.1 surface is a Mathlib-only Challenge, a text-identical Solution holding `_of`
forms, and a well-formed configuration. Nothing checks it, builds it or describes it:
- no statement-match or axiom driver;
- no lakefile library;
- no gate entry;
- no workflow step;
- no metadata;
- no README section.

The hypothesis-free endpoint is owed by pc-assembly.

Expected editorial grading once the gaps close:
- Notability: the question is printed in Pestov's survey and originates with Ozawa, and the audience is operator
  algebras (Connes embedding and LLP, via Ozawa) and approximation of groups. That is the anchor "unusually
  consequential, with clear interest beyond a narrow specialist audience".
- The risks are F6 (the Dadarlat sentence) and F7 (the bounded search). Both are presentation gaps that can be
  corrected.
