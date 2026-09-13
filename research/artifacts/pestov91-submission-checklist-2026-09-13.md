# Pestov 9.1 Palomar submission checklist (2026-09-13)

Lane `pc-integrate`. **Version 2, not submittable.** Each item carries its evidence: a commit on main, a GitHub
Actions run id, or a probe record with its axiom lines. An item without evidence is OPEN, and the item says what it
waits on.

**Ownership.** The fz swarm (session 6dbfc571), lane `fz-integrate`, owns the Pestov 9.1 formalization and its
integration: root imports, lakefile, gate script, the project header, scope, main_results, alignment, README, the final
root probe and the Comparator dispatch. `pc-integrate` owns the formalization.yaml `sources`, credit and `fidelity`
rows where those are missing or wrong, and this file.

**Question.** V. G. Pestov, *Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic Logic 14 (2008),
arXiv:0804.3968, p. 21: "Open question 9.1 (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's
property (T). Can it be hyperlinear (sofic)?"

**Submission tuple.** Repository `SauersML/group-approximation`, commit OPEN, configuration
`Palomar/comparator-pestov91.json`.

**Left to the user.** The registry submission is the web form at https://submit.palomar-registry.org, naming the
repository, one immutable commit and the configuration path. No lane submits it.

## 1. Statement surface

1. **Challenge, `Palomar/Pestov91Challenge.lean`**, unchanged since b490bf08d:
   - Mathlib-only imports;
   - 149 lines;
   - the question quoted verbatim;
   - holes `exists_infinite_simple_propertyT_hyperlinear` and `exists_infinite_simple_propertyT_sofic`.

   OPEN: pc-palomar's third compared theorem, `exists_infinite_simple_propertyT_sofic_hyperlinear`, is not on main at
   798be51a3.
2. **Solution, `Palomar/Pestov91Solution.lean`**, unchanged since 8f4501419. It holds only
   `exists_infinite_simple_propertyT_hyperlinear_of` and `exists_infinite_simple_propertyT_sofic_of`. Both take an
   infinite simple Kazhdan LEF group as a hypothesis, so they are conditional. OPEN.
3. **Configuration** at b490bf08d: two theorem names, `permitted_axioms` propext, Quot.sound and Classical.choice.
   OPEN: it follows item 1. The metadata rows go in configuration order (pc-registry).
4. **Gate registration as pending** at 764023101: the `PALOMAR_PENDING_CONFIGS` entry, the lean_libs (not default
   targets), and the palomar-check build and axiom-driver step. The Comparator workflow builds the pair. OPEN: the move
   to `PALOMAR_CONFIGS`.

## 2. Development

5. **Endpoint**, OPEN: no binder-free theorem at 798be51a3; `Assembly.lean` has only `_of` forms. Landed since
   version 1:
   - `RingFinitelyGenerated` (622570981): LC(X, ZMod 2) ⋊ ℤ is a finitely generated ring;
   - `WitnessCentre` (8443d297e): the central elements of LC(X, F₂) ⋊ ℤ are 0 and 1;
   - `SimpleModCentre` (c3cfee844): EL_n(R)/Z is simple for simple rings with local annihilation.
6. **Axiom closure of the endpoint**, OPEN. The palomar-check Pestov 9.1 driver step passes (runs 34746055734 and
   34746551805), but the driver's theorems are the pending `_of` forms, so this is not the endpoint's closure.
7. **Root wiring**, OPEN, owned by fz-integrate. 35c746f8e imports 7 of the 13 modules from the root: Assembly,
   CrossedProductFG, KazhdanUnitary, LEFHyperlinear, RingFinitelyGenerated, RingSimple and SplitSimplicity. Of the rest:
   - Centre, CentreSkew, CrossedProduct and Kazhdan are in the root closure through their importers;
   - `SimpleModCentre` and `WitnessCentre` are imported by nothing at 798be51a3, so they lie outside the root closure.

## 3. Metadata and prose

8. **`formalization.yaml` sources and credit**, at 30af467bac (2026-09-13 03:07:13 CDT, yaml blob 01b78f8419).
   - **Rows.** 53 sources, 3 original-proof rows, 0 substantive relationships.
   - **Literature**, since c4006e2168: the 13 rows of pc-lit-background's final set. Pestov's guide,
     Ershov-Jaikin-Zapirain, Elek-Szabo 2004 and Bekka-de la Harpe-Valette each gain one sentence.
   - **Original-proof row**, "An infinite simple group with property (T) that is sofic and hyperlinear", since
     30af467bac. It is pc-priority-credit's final text
     (`research/artifacts/pestov91-priority-credit-2026-09-13-rows.yaml`, 2a5ddc58fc).
     - Contributor: Claude (Anthropic), who solved the problem, reviewed the proof independently twice and wrote the
       prose.
     - The question: Ozawa asks it in arXiv:math/0306067v1 (2003-06-03). Pestov prints it as 8.1 in v1 (2008-04-24)
       and as 9.1 in v8 (2008-08-04). Arzhantseva (2014) still lists the sofic form as unknown.
     - Commit author dates, UTC: f375478c7 03:18:24; 0efeac410 03:48:55; 8b65f0932 04:09:24; badc66e2d 05:56:33.
       A second-session agent found the same group independently, 5dfab98df at 04:06:49.
     - The search bound: LaTeX sources of more than twenty papers; the Kirchberg, Arzhantseva and Pisier PDFs;
       OpenAlex citer abstracts. arXiv was rate-limited and journal versions were not opened.
   - **Held until the endpoint lands.**
     - From the origin note: the endpoint and Palomar landing sentence, and "formalised with q = 2".
     - pc-priority-credit's `automation.methods` entry, `automation.notes` paragraph and README credit paragraph. They
       state Lean completion.
     - Recheck then that `GroupApproximation/Pestov91/Kazhdan.lean` is still the Claude Opus 5 blob of 8829513da.
   - **Held until their modules land.** Jacobs-Keane waits on the subshift module. The Grigorchuk-Medynets clause
     "the development proves that ring version" waits on `RingLEFSubshift`.
   - **Fidelity paragraph.** OPEN, owed by pc-review.
   - **fz-integrate's rows, at the move** (pc-registry item 0): the header, `status.scope`, `main_results`, `proved`
     alignment rows and README claim land only in the change that moves the configuration to `PALOMAR_CONFIGS`.
9. **README**, OPEN, owned by fz-integrate. pc-priority-credit's credit paragraph is ready for it.
10. **Prose accuracy notes** for any informal proof account. The registry compares the account with the Lean present.
    - Simplicity in the Lean is root detection without division:
      - `SplitSimplicity.lean`, with split annihilators;
      - `SimpleModCentre.lean`, with local annihilation.

      It is not the write-up's tower-and-absorption route.
    - The docstrings name the witness as `EL₃(R)/Z(EL₃(R))` over `𝔽_q` in some modules and as `EL₃(R)` over `𝔽₂` in
      others. The two agree because the centre is trivial over `𝔽₂`.
    - The prose credit line is missing from most modules.
    - `RingSimple.lean` cites Brown-Clark-Farthing-Sims, whose theorem is over ℂ. The field-general statements are
      Clark-Edie-Michell Corollary 4.6 and Steinberg Corollary 3.6.
    - pc-registry: claim no finite generation or presentation of the witness unless a Lean theorem states it.

## 4. Checks

11. **`palomar-check`.**
    - **The rename fixed the gate.**
      - Before: runs 34743705887, 34743870806, 34744000162, 34744098007, 34744290964 and 34745087732 failed on the
        tracked `attic/gottschalk-swarm-2026-09-12/sweep/ugc.O`.
      - The fix: b78e01714 renames it to `ugc.O.txt` with the same blob, 0bb17bf1ad.
      - After: run 34746055734 on 4a99816303 (07:46:39Z to 07:53:19Z) succeeded at every step: the submission gate,
        the Palomar build, statement match, and the axiom drivers for non-MF, LIX, strengthened LIX, Bowen-Chapman,
        Pestov 9.1 and FFWZ 5.8.
    - **The three-origin source list passes the metadata gate.** Run 34746551805 on c4006e216 succeeded at the same
      steps.
12. **Comparator with NanoDa** on `config=Palomar/comparator-pestov91.json`: OPEN, dispatched by fz-integrate after
    items 2 to 7. No run has used this configuration. The latest Comparator runs, 34735545983 and 34734709860, are
    Bowen-Chapman successes.
13. **Carry-over** from the Comparator commit to the submission commit: OPEN.

## 5. Reviews and records

14. **Statement fidelity and model tests** [pc-review]: OPEN.
15. **Literature** [pc-lit-background]: `research/artifacts/pestov91-literature-background-2026-09-13.md` and parts
    2–4 (62f139b74f). Within the stated bound, no source answers Question 9.1 earlier.
16. **Priority and credit** [pc-priority-credit]: `research/artifacts/pestov91-priority-credit-2026-09-13.md`
    (d76d85dbed), `-part2.md` (df17807b48), `-part3.md` and `-rows.yaml` (2a5ddc58fc).
    - The earliest printed ask is Ozawa, arXiv:math/0306067v1 (2003-06-03).
    - The construction first appears in the records of the lane that landed it. No custom proof tool appears.
17. **Registry simulation** [pc-registry], lane file `$PC/lanes/pc-registry/pestov91-registry-gaps.md`:
    - No notability finding is predicted.
    - Sequencing rule: item 8 above.
    - No MSC swap is needed; `math.RA` is optional.
    - Every relationship must stay background or other.
    - The `review.notes` pointers must exist at the submitted commit.
