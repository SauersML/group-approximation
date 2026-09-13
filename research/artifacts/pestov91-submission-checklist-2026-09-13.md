# Pestov 9.1 Palomar submission checklist (2026-09-13)

Lane `pc-integrate`. **Version 1, not submittable.** Each item carries its evidence: a commit on main, a GitHub
Actions run id, or a probe record with its axiom lines. An item without evidence is OPEN, and the item says what it
waits on.

**Ownership.** The fz swarm (session 6dbfc571), lane `fz-integrate`, owns the Pestov 9.1 formalization and its
integration: root imports, lakefile, gate script, formalization.yaml and README rows, the final root probe, and the
Comparator dispatch. The PC swarm's lanes land modules and reviews. This file tracks progress. `pc-integrate` fills
formalization.yaml `sources`, credit and `fidelity` rows only where the integrating lane's rows are missing or wrong.

**Question.** V. G. Pestov, *Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic Logic 14 (2008),
arXiv:0804.3968, p. 21: "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's
property (T). Can it be hyperlinear (sofic)?"

**Submission tuple.** Repository `SauersML/group-approximation`, commit OPEN, configuration
`Palomar/comparator-pestov91.json`.

**Left to the user.** The registry submission is the web form at https://submit.palomar-registry.org, naming the
repository, one immutable commit and the configuration path. No lane submits it.

## 1. Statement surface

1. **Challenge, `Palomar/Pestov91Challenge.lean`**, last changed at b490bf08d:
   - imports Mathlib only, seven `Mathlib.*` imports;
   - is 149 lines;
   - quotes the question verbatim;
   - states `exists_infinite_simple_propertyT_hyperlinear` and `exists_infinite_simple_propertyT_sofic` as deliberate
     holes.

   pc-palomar is adding a third compared theorem, `exists_infinite_simple_propertyT_sofic_hyperlinear`; it is
   unlanded at 1c5f36398.
2. **Solution, `Palomar/Pestov91Solution.lean`**, last changed at 8f4501419. It proves only
   `exists_infinite_simple_propertyT_hyperlinear_of` and `exists_infinite_simple_propertyT_sofic_of`. Both take an
   infinite simple Kazhdan LEF group as a hypothesis, so they are conditional. OPEN: the binder-free theorems.
3. **Configuration, `Palomar/comparator-pestov91.json`**, at b490bf08d. `theorem_names` are the two names of item 1,
   and `permitted_axioms` are propext, Quot.sound and Classical.choice. OPEN: follows item 1.
4. **Gate registration, as pending**, at 764023101:
   - `scripts/check_palomar_submission.py` lists the configuration in `PALOMAR_PENDING_CONFIGS`;
   - `lakefile.toml` declares `PalomarPestov91Challenge` and `PalomarPestov91Solution`, not as default targets;
   - `palomar-check.yml` builds the pair and runs `scripts/PalomarPestov91Axioms.lean` as its own step;
   - `palomar-comparator.yml` builds the pair;
   - the statement-match script and the type drivers cover it.

   OPEN: moving the configuration to `PALOMAR_CONFIGS`, in the same change as the `status.main_results` rows, once
   the solution has no hypothesis.

## 2. Development

5. **Endpoint**, OPEN: no binder-free theorem is on main at 1c5f36398. The blueprint pins
   `exists_infinite_simple_kazhdan_sofic_hyperlinear : ∃ (G : Type) (_ : Group G), Infinite G ∧ IsSimpleGroup G ∧
   HasKazhdanPropertyT.{0, 0} G ∧ IsSofic G ∧ IsHyperlinear G`, with witness `EL₃(LC(X, 𝔽₂) ⋊ ℤ)` for the orbit
   closure of the period-doubling sequence. `GroupApproximation/Pestov91/Assembly.lean` has only `_of` forms.
6. **Axiom closure**, OPEN. No probe record for the endpoint exists. `status.main_results` is copied from that
   record's `# axioms` lines and from nothing else.
7. **Root wiring**, OPEN, owned by fz-integrate. At 1c5f36398 main holds 11 `GroupApproximation/Pestov91/*.lean`
   modules. The root imports one of them, `GroupApproximation.Pestov91.RingFinitelyGenerated` (622570981).

## 3. Metadata and prose

8. **`formalization.yaml`**, OPEN, owned by fz-integrate. At 8437044358 (blob 7b463d3f14) it has no Pestov 9.1 row.
   Inputs owed to pc-integrate for the gap-filling rows: sources from pc-lit-background, credit and timeline from
   pc-priority-credit, fidelity from pc-review.
9. **README**, OPEN, owned by fz-integrate: no section for this result yet.
10. **Prose accuracy notes** for whoever writes the informal proof account. The registry's proof_account step
    compares any informal account with the Lean actually present.
    - Simplicity of `EL₃(R)` in the Lean is `GroupApproximation/Pestov91/SplitSimplicity.lean`: root detection without
      division.
      - `Leavitt.RootDetectionBinary` supplies the root.
      - `crossedProduct_split_annihilator` proves the split-annihilator input.
      - `isSimpleGroup_elementaryGroup_of_split` closes the argument through `normalLevel` and `IsSimpleRing R`.

      It is not the write-up's tower-and-absorption route (pc-registry, at 6965e0292).
    - The module docstrings name the witness three ways:
      - `EL₃(R)/Z(EL₃(R))` over `𝔽_q` in Assembly, Centre, CrossedProduct and Kazhdan;
      - `EL₃(R)` over `𝔽₂` in SplitSimplicity and the blueprint;
      - the two agree only because the centre is trivial over `𝔽₂`.
    - The prose credit line is in Assembly and the Palomar pair only.
    - RingSimple cites Brown–Clark–Farthing–Sims, whose simplicity theorem is over ℂ. The field-general statements
      are Clark–Edie-Michell, arXiv:1403.4684, Corollary 4.6, and Steinberg, arXiv:1408.6014, Corollary 3.6.

## 4. Checks

11. **`palomar-check`**: the blocker is removed; OPEN until a run on a commit containing b78e01714 completes.
    - Runs 34743705887 (398373fe3), 34743870806 (b490bf08d), 34744000162 (c52176461), 34744098007 (24ed18bcf) and
      34744290964 (8f4501419) failed on one gate finding: "attic/gottschalk-swarm-2026-09-12/sweep/ugc.O is a compiled
      artifact and is tracked". The Lean steps were skipped, and the four axiom drivers reported "lake: command not
      found".
    - b78e01714 (2026-09-13 02:33:57 CDT) renames that file to `ugc.O.txt`. The blob 0bb17bf1ad is unchanged, and the
      commit changes exactly those two paths. It is on the remote tip, and the old path is absent there.
12. **Comparator with NanoDa** on `config=Palomar/comparator-pestov91.json`, OPEN, dispatched by fz-integrate after
    items 2 to 7. No Comparator run has used this configuration yet. The latest runs are the Bowen-Chapman ones,
    34735545983 and 34734709860, both successful.
13. **Carry-over** from the Comparator commit to the submission commit, OPEN.

## 5. Reviews and records

14. Statement fidelity and model tests [pc-review]: OPEN.
15. Literature and background [pc-lit-background]: OPEN. On main already:
    `research/artifacts/ex-novelty-pestov91-deep-pass-2026-09-12.md` and
    `research/artifacts/pestov-9-1-writeup-2026-09-13-part3.md` §10, both bounded searches that found no earlier
    answer.
16. Priority and credit [pc-priority-credit]: OPEN.
17. Registry simulation [pc-registry]. Classification advice: change no MSC code; `math.GR`, `20F65` and `22D55`
    already describe the result, and `math.RA` is an optional fifth arXiv class. Also the proof-account finding
    recorded in item 10.
