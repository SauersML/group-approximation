# Pestov 9.1 Palomar submission checklist (2026-09-13)

Lane `pc-integrate`. **Version 0, not submittable.** Each item carries its evidence: a commit on main, a GitHub
Actions run id, or a probe record with its axiom lines. An item without evidence is OPEN, and the item says what it
waits on. Later versions of this file replace OPEN entries with evidence.

**Question.** V. G. Pestov, *Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic Logic 14 (2008),
arXiv:0804.3968, p. 21: "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's
property (T). Can it be hyperlinear (sofic)?"

**Submission tuple.** Repository `SauersML/group-approximation`, commit OPEN, configuration
`Palomar/comparator-pestov91.json`.

**Left to the user.** The registry submission is the web form at https://submit.palomar-registry.org, naming the
repository, one immutable commit and the configuration path. No lane submits it.

## 1. Statement surface [pc-palomar]

1. **Challenge, `Palomar/Pestov91Challenge.lean`**, last changed at b490bf08d. At 9a005f042 it:
   - imports Mathlib only, seven `Mathlib.*` imports;
   - is 149 lines;
   - quotes the question verbatim in its docstring;
   - states `exists_infinite_simple_propertyT_hyperlinear` and `exists_infinite_simple_propertyT_sofic` as
     deliberate holes.

   OPEN: pc-palomar's redesign merges them into one theorem, `exists_infinite_simple_kazhdan_sofic_hyperlinear`.
2. **Solution, `Palomar/Pestov91Solution.lean`**, last changed at 8f4501419. At 9a005f042 it proves only
   `exists_infinite_simple_propertyT_hyperlinear_of` and `exists_infinite_simple_propertyT_sofic_of`. Both take the
   hypothesis `∃ E, Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0,0} E ∧ IsLEF E`, so they are conditional.
   A token scan of `GroupApproximation/Pestov91/` and the Solution at 9a005f042 finds no proof placeholder and no
   axiom declaration. OPEN: the binder-free theorems.
3. **Configuration, `Palomar/comparator-pestov91.json`**, at b490bf08d. `theorem_names` are the two names of item 1,
   and `permitted_axioms` are propext, Quot.sound and Classical.choice. OPEN: follows item 1.
4. **Gate registration**, OPEN. At 9a005f042:
   - `scripts/check_palomar_submission.py` (last changed d54fa7120) lists the configuration in neither
     `PALOMAR_CONFIGS` nor `PALOMAR_PENDING_CONFIGS`;
   - `lakefile.toml` (c1e3df1ef) has no `lean_lib` for the pair;
   - `palomar-comparator.yml` and `palomar-check.yml` (c1e3df1ef) build only the LIX, strengthened LIX,
     Bowen-Chapman and non-MF libraries.

   So a Comparator dispatch on this configuration today would fail on a missing module, not on the submission.

## 2. Development [pc-assembly and module owners]

5. **Endpoint**, OPEN. `GroupApproximation/Pestov91/Endpoint.lean` is not on main. The blueprint pins
   `exists_infinite_simple_kazhdan_sofic_hyperlinear : ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧
   HasKazhdanPropertyT.{0, 0} G ∧ IsSofic G ∧ IsHyperlinear G`, with witness `EL₃(LC(X, 𝔽₂) ⋊ ℤ)` for the orbit
   closure of the period-doubling sequence. `GroupApproximation/Pestov91/Assembly.lean` has only the `_of` forms,
   which take finite generation, simplicity and infiniteness as hypotheses.
6. **Axiom closure**, OPEN. No probe record for the endpoint exists. The only PC probe record so far is pc-infra's
   calibration, `pc-infra.green.0913-020954-89615`. `status.main_results` will be copied from the endpoint record's
   `# axioms` lines and nothing else.
7. **Root wiring**, OPEN. At b8441172e main holds 10 `GroupApproximation/Pestov91/*.lean` modules and
   `GroupApproximation.lean` imports none of them. The landings 8829513da, 5f444f257, e3200c6c2, 03c0f1a39,
   f3b198106, 89448ad3b, d946a358a and 21147debe each touched only their own module.

## 3. Metadata and prose [pc-integrate]

8. **`formalization.yaml`**, OPEN, last changed 2720752d2 and describing LIX and Bowen-Chapman only. It needs:
   - the project header for three results;
   - an original-proof row;
   - background rows, and extended notes on the Pestov, Ershov-Jaikin-Zapirain, Elek-Szabo and
     Bekka-de la Harpe-Valette rows;
   - automation, review, scope, main_results (from item 6), fidelity, alignment and classification.

   Inputs owed: sources from pc-lit-background, credit and timeline from pc-priority-credit, fidelity and alignment
   from pc-review, policy gaps from pc-registry.
9. **README**, OPEN, last changed 15c160c7b. It needs a section for the result, and the list of configurations must
   name the third.
10. **Module docstrings**, OPEN.
    - The witness is described as `EL₃(R)/Z(EL₃(R))` over `𝔽_q` in Assembly, Centre, CrossedProduct and Kazhdan, and
      as `EL₃(R)` over `𝔽₂` by the blueprint and SplitSimplicity.
    - The prose credit line is in Assembly, the Challenge and the Solution only.

    The fixes land as one docstring-only batch after the endpoint lands.

## 4. Checks [pc-integrate]

11. **`palomar-check`**, OPEN and currently red for a reason unrelated to this surface. Runs 34743705887
    (398373fe3), 34743870806 (b490bf08d), 34744000162 (c52176461), 34744098007 (24ed18bcf) and 34744290964
    (8f4501419) all fail the same way:
    - the submission gate's one finding is "attic/gottschalk-swarm-2026-09-12/sweep/ugc.O is a compiled artifact
      and is tracked", a file landed by 5e3b2f7eb and still on main at b8441172e;
    - so the Lean steps are skipped, and the four axiom drivers fail with "lake: command not found".

    Reported to main.
12. **Comparator with NanoDa** on `config=Palomar/comparator-pestov91.json`, OPEN; it waits on items 2 to 6. No
    Comparator run has used this configuration. The latest runs are the Bowen-Chapman ones, 34735545983 and
    34734709860, both successful.
13. **Carry-over** from the Comparator commit to the submission commit, OPEN.

## 5. Reviews and records

14. Statement fidelity and model tests [pc-review]: OPEN.
15. Literature and background [pc-lit-background]: OPEN. On main already:
    `research/artifacts/ex-novelty-pestov91-deep-pass-2026-09-12.md` and
    `research/artifacts/pestov-9-1-writeup-2026-09-13-part3.md` §10, both bounded searches that found no earlier
    answer.
16. Priority and credit [pc-priority-credit]: OPEN.
17. Registry simulation [pc-registry]: OPEN.
