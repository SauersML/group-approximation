# Pestov 9.1 Palomar submission checklist (2026-09-13)

Lane `pc-integrate`. Version 3 is by lane `ex-palomar-hygiene`, merged onto version 2 (blob 2d50d67cf0).

**Status.**
- The surface is complete and certified. The endpoint is binder-free, the configuration is submitted, and the
  Comparator passes.
- Open, and blocking: only the user's registry submission. The Comparator and palomar-check pass on e5783d06f, which
  contains every change so far (item 13).
- Open, not blocking: one credit question in item 8, one README paragraph, and optional docstring credits in item 10.

Each item carries its evidence: a commit on main, a GitHub Actions run id, or a probe record. An item without evidence
is OPEN, and the item says what it waits on.

**Ownership.** The fz swarm (session 6dbfc571), lane `fz-integrate`, owns the Pestov 9.1 formalization and its
integration: root imports, lakefile, gate script, the project header, scope, main_results, alignment, README, the final
root probe and the Comparator dispatch. `pc-integrate` owns the formalization.yaml `sources`, credit and `fidelity`
rows where those are missing or wrong, and this file.

**Question.** N. Ozawa, *About the QWEP conjecture*, arXiv:math/0306067 v1 (2003), asks it first. V. G. Pestov prints it
with the sofic form added in *Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic Logic 14 (2008),
arXiv:0804.3968v8, p. 21: "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's
property (T). Can it be hyperlinear (sofic)?"

**Submission tuple.**
- Repository: `SauersML/group-approximation`.
- Commit: e5783d06f, or any later commit on which this configuration's Comparator run passes (item 13).
- Configuration: `Palomar/comparator-pestov91.json`.

**Left to the user.** The registry submission is the web form at https://submit.palomar-registry.org, naming the
repository, one immutable commit and the configuration path. No lane submits it.

## 1. Statement surface

1. **Challenge, `Palomar/Pestov91Challenge.lean`.** DONE.
   - Mathlib-only imports.
   - Two holes: `exists_infinite_simple_propertyT_hyperlinear` and `exists_infinite_simple_propertyT_sofic`.
   - pc-palomar's third theorem (the joint form) was not adopted; the configuration compares the two forms.
   - 7bbaa02ac and ce417f2d3 changed only comments and docstrings. They quote Ozawa first, and they add the paragraph
     citing Pestov's Definitions 3.1–3.2 and Theorems 3.5–3.6 (literature part 3, §E2). The comment-stripped code is
     identical to e32bac3f3.
2. **Solution, `Palomar/Pestov91Solution.lean`.** DONE at 5f9c16b7b.
   - `exists_infinite_simple_propertyT_hyperlinear` and `exists_infinite_simple_propertyT_sofic` are proved without
     hypotheses from `GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef`.
   - The conditional `_of` forms remain alongside them.
3. **Configuration.** DONE.
   - Two theorem names; `permitted_axioms` propext, Quot.sound and Classical.choice.
   - Submitted at c2cbd9e3e (09:51:59 UTC): the entry is in `PALOMAR_CONFIGS` of `scripts/check_palomar_submission.py`,
     and `PALOMAR_PENDING_CONFIGS` is empty.
4. **Gate registration.** DONE. The palomar-check workflow builds `PalomarPestov91Challenge`, `PalomarPestov91Solution`
   and `PalomarPestov91ModelTests`, and runs `scripts/PalomarPestov91Axioms.lean`.

## 2. Development

5. **Endpoint.** DONE at 5f9c16b7b (08:43:33 UTC). `GroupApproximation/Pestov91/WitnessAssembly.lean`,
   `exists_infinite_simple_kazhdan_lef`: some `E : Type` with a group structure is infinite, simple, Kazhdan and LEF.
   It takes no binders.
   - The witness is `EL₃(LC(X, 𝔽₂) ⋊ ℤ)` over the Toeplitz subshift, from `witnessRing_isFinitelyGeneratedRing` and
     `witnessRing_isLEFRing` (`LEFWitness.lean`).
   - The centre is trivial, so no quotient is taken.
6. **Axiom closure.** DONE.
   - Comparator on `config=Palomar/comparator-pestov91.json` passed, with only the permitted axioms: run 34751904895
     (e32bac3f3), 34761506719 (7bbaa02ac), 34762709305 (be41521bf) and 34763215377 (e5783d06f).
   - The palomar-check driver step passes: 34762687202 (be41521bf) and 34763187094 (e5783d06f).
7. **Root wiring.** DONE. The root imports all 25 modules of `GroupApproximation/Pestov91/`.

## 3. Metadata and prose

8. **`formalization.yaml`.** Rows by fz-integrate, plus pc-integrate's held rows released at 9f0d94a0d.
   - **Original-proof row.**
     - Credit: Claude (Anthropic), no custom proof tool.
     - Timeline f375478c7, 0efeac410, 8b65f0932, badc66e2d and 5dfab98df.
     - Released at 9f0d94a0d: "The Lean endpoint GroupApproximation.Pestov91.exists_infinite_simple_kazhdan_lef landed
       with the completed Palomar surface at 08:43:33 UTC (5f9c16b7b). All of this postdates …".
     - "q = 2 with X the Toeplitz subshift" was already on main.
   - **Sources.**
     - Jacobs-Keane, *0-1-sequences of Toeplitz type*: on main, pointing at `Toeplitz.lean`. The pd-subshift condition
       of the held row is moot: the witness uses the Toeplitz sequence `decide (padicValInt 2 (3n − 1) odd)`.
     - Grigorchuk-Medynets: released at 9f0d94a0d, "the development proves that ring version and does not use this
       theorem".
     - Brown-Clark-Farthing-Sims (over ℂ), Clark-Edie-Michell Corollary 4.6 and Steinberg Corollary 3.6: on main.
   - **Review, scope, main results and fidelity.** On main:
     - `review.notes` points at both review artifacts;
     - `status.scope` and `main_results` list the two declarations with the configuration;
     - the fidelity section has the Pestov paragraph.
   - **Automation.** The Pestov paragraph on main says the formalisation belongs to the third methods entry, whose
     models are `[Claude (Anthropic)]`. pc-priority-credit's methods entry and paragraph are superseded by it.
   - **OPEN, credit** (fz-integrate):
     - `GroupApproximation/Pestov91/Kazhdan.lean` is still the blob of 8829513da.
     - `research/artifacts/pestov91-priority-credit-2026-09-13-part3.md` records that module as written by a Claude Opus 5
       agent.
     - The automation paragraph and models list do not name Claude Opus 5. Decide from the transcripts whether they
       should.
9. **README.**
   - Pestov section: on main.
   - OPEN (fz-integrate): pc-priority-credit's credit paragraph (`pestov91-credit.yaml`, `readme_credit_paragraph`) is
     not in the section. If it is added, use the endpoint 5f9c16b7b and take the Opus 5 clause from item 8's decision.
10. **Prose accuracy.**
    - `RingSimple.lean` cites the field-general criterion (Clark-Edie-Michell Corollary 4.6, Steinberg Corollary 3.6),
      with BCFS over ℂ as its origin: 95632338d.
    - `Assembly.lean` pins arXiv:0804.3968v8: 33c61859c, probe GREEN 0913-091934-38820.
    - OPEN, optional: the Challenge docstring still says "(arXiv:0804.3968), Section 9, page 21" without v8 (literature
      part 3, §E1). A change there moves the submission commit, item 13.
    - OPEN, optional (§E4): name the Ershov-Jaikin-Zapirain reference (Invent. Math. 179 (2010), arXiv:0809.4095v2,
      Theorem 1.1) in `Kazhdan.lean` and `CrossedProductFG.lean`, and Elek-Szabó in `LEFHyperlinear.lean`.
    - Simplicity in the Lean is root detection without division (`SplitSimplicity.lean`, `SimpleModCentre.lean`), not
      the write-up's tower-and-absorption route. An informal account for the registry should say so.
    - pc-registry: claim no finite generation or presentation of the witness beyond the Lean theorems.

## 4. Checks

11. **`palomar-check`.** DONE. It passes at e5783d06f (34763187094), be41521bf (34762687202), ce417f2d3 (34761988439)
    and 7bbaa02ac (34761488911).
    - That run builds `Palomar.Pestov91ModelTests` from source, after `lake exe cache get`, and prints its 22 axiom
      closures.
    - Every incomplete-proof warning in that run comes from a `*Challenge.lean` file.
12. **Comparator with NanoDa.** DONE on the three commits of item 6.
13. **Carry-over to the submission commit.** DONE for e5783d06f.
    - Since be41521bf, the only change to the surface or the development is the Assembly docstring (33c61859c).
    - e5783d06f contains it, and there the pestov91 Comparator (34763215377) and palomar-check (34763187094) pass.
    - Any later change to `Palomar/Pestov91*`, `GroupApproximation/Pestov91/`, the lakefile or the manifest needs a new
      run before a later commit is submitted.

## 5. Reviews and records

14. **Statement fidelity and model tests.**
    - `Palomar/Pestov91ModelTests.lean` landed at be41521bf; the commit says it bridges all three conditions of Pestov's
      Theorem 3.6. Evidence: item 11.
    - The fidelity paragraph is on main.
15. **Literature** [pc-lit-background]. `research/artifacts/pestov91-literature-background-2026-09-13.md` and parts 2–4.
    Within the stated bound, no source answers Question 9.1 earlier.
16. **Priority and credit** [pc-priority-credit]. `research/artifacts/pestov91-priority-credit-2026-09-13.md`,
    `-part2.md`, `-part3.md` and `-rows.yaml`. The earliest printed ask is Ozawa, arXiv:math/0306067v1 (2003-06-03).
17. **Registry simulation** [pc-registry]. `research/artifacts/pestov91-registry-review-2026-09-13.md` and `-part2.md`.
    No MSC swap is needed, and every relationship stays background or other.
18. **Probe evidence after the artifact-restore defect.** `research/artifacts/probe-false-green-recheck-2026-09-13.md`
    (d3f6c39f59).
    - No landed Pestov 9.1 Palomar module rests on a false green: every Pestov91 Solution and driver record shows the
      module Built.
    - The probe templates are fixed on MSI.
