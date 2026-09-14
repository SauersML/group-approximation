# STW XXII Palomar submission readiness

Prepared September 13, 2026 America/Chicago (September 14 UTC).
**Status: READY FOR SUBMISSION. All preparation and exact-revision checks passed. NOT SUBMITTED.**

## Immutable candidate

- Repository: https://github.com/SauersML/group-approximation
- Commit: `637ae0c8446d073e1e1000e54a924742cc6f7041`
- Public tag: [`palomar-stw-xxii-20260913-v3`](https://github.com/SauersML/group-approximation/tree/palomar-stw-xxii-20260913-v3)
- Project directory: repository root; no project-path override.
- Metadata: `formalization.yaml` (identical result-specific copy: `metadata/palomar-stw-xxii.yaml`).
- Comparator configuration: `Palomar/comparator-stw-xxii.json`.
- Author: Sauers. Responsible maintainer: SauersML. License: Apache-2.0.
- Public title: **A Counterexample to the Trace Problem for Uniform Tracial Completions**.

The commit above is the candidate to submit. It supersedes the preliminary
`fa325e08c4566ca3a46e2d8fa2ed04463a2b74c2` candidate by adding literature
credit and question history; the entire Lean source tree is unchanged
between these two candidates. Subsequent documentation commits
and activity on main do not change it. The root metadata on a moving main
branch may describe another submission; always use this exact candidate. This readiness record is maintained
separately so it can identify verification of the candidate without changing
the candidate's SHA.

## Selected mathematical content

`STWProblemXXII.exists_uniformTracialCompletion_with_discontinuous_trace`
asserts that a separable unital C*-algebra A has nonempty compact trace space
and a uniform tracial completion M with an additional trace. The designated
traces X are exactly the uniform-two-continuous ones and are a proper subset
of T(M). The completion is stated by its presentation: tracial completeness,
unique restriction to every base trace, and uniform-two density.

`STWProblemXXII.exists_factorial_traciallyComplete_with_discontinuous_trace`
asserts the corresponding failure for a factorial tracially complete pair
(M, X), again identifying the continuous traces with X.

The two statements answer STW Problem XXII and CCEGSTW Question 1.1,
respectively. They are unconditional. Their selected scope does not include
nuclearity, type I, the Bauer property, or simplicity. The actual construction
and the source/statement alignment are described in the candidate's metadata.

## Verification

| Check | Result / evidence |
|---|---|
| Source/configuration/metadata gate | PASS, local Python 3.13 with PyYAML 6.0.3 |
| Gate calibration | PASS: clean copy accepted; all 51 planted defects detected; zero skipped |
| Upstream metadata v0.4 JSON schema | PASS, jsonschema 4.25.1 |
| Current metadata equals per-result archive | PASS, byte-identical |
| Challenge review surface | 184 lines; 10,771 UTF-8 bytes; below preferred limits |
| Mathlib dependency pins | PASS: all eight transitive package URL/SHA pairs exactly match canonical Mathlib manifest |
| Mathematical changes in preparation | Initial four Lean edits were comments only; source token comparison passed. Final literature revision changes no Lean files at all. |
| Public candidate tag | Resolves to the exact candidate SHA |
| Entire committed Lean/toolchain input comparison | PASS: all 7,254 entries match the earlier kernel-accepted candidate |
| Exact-revision build, models, statements and axioms | PASS: [Palomar check 34803475771](https://github.com/SauersML/group-approximation/actions/runs/34803475771) |
| Exact-revision Comparator, Lean and NanoDa replay | PASS: [Comparator 34803475769](https://github.com/SauersML/group-approximation/actions/runs/34803475769), config=Palomar/comparator-stw-xxii.json, nanoda=true |

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The Challenge deliberately has two `sorry` placeholders, one for each selected
statement. The exact-revision axiom audit proves that both Solution closures
contain precisely the three permitted axioms, with no `sorryAx`.
The calibration stage deliberately prints diagnostics for planted defects;
those are expected, and its clean-tree acceptance and all 51 detections pass.
Repository verification is distinct from the registry's future verification
and editorial review. No Palomar acceptance is claimed.

## Saved verification evidence

Both final GitHub Actions runs report head SHA
`637ae0c8446d073e1e1000e54a924742cc6f7041` and conclusion `success`.
Comparator completed on September 14, 2026 at 03:54:55 UTC.
The saved Comparator artifact was downloaded and inspected for both selected
declaration names, both kernel acceptance messages, and the final verdict:

```text
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

The separate XXII axiom step printed exactly
`axiom closure (3): [propext, Classical.choice, Quot.sound]`
for each selected theorem. The source gate accepted the clean tree and
all 51 planted-defect calibrations were detected with zero skipped.

- Comparator artifact: `comparator-log` on
  [run 34803475769](https://github.com/SauersML/group-approximation/actions/runs/34803475769).
- Comparator log SHA-256: `1ba49e750486964262b1dedd71a985bf44015a478c94d051ad41976c662d0e70`.
- Full Palomar-check log SHA-256: `85a6c0ca30be6f8b6848db0d9faf9a3e59dafae80f29b91ca84a7031491bdc05`.

## Fidelity and provenance review

The presentation in the Challenge matches CCEGSTW Corollary 3.29(i): for a
uniform-two-dense C*-subalgebra of a tracially complete pair, completion at
the restricted traces recovers the pair. The restriction clause identifies
those traces with all of T(A); possible kernel elements are null for all base
traces. The algebraic image of a C*-homomorphism is a C*-algebra and bounded
image elements have bounded lifts. Thus the presentation characterizes the
usual bounded-Cauchy completion. The proof's witness is that quotient itself.

The preparation corrects old module comments that incorrectly called
factoriality an additional hypothesis of printed XXII. It is a consequence
of completing at all traces; it is an explicit hypothesis in the more general
CCEGSTW Question 1.1. Definitions, theorem statements, and proofs were unchanged.
The existing positive and negative definition models are built by the gate.

The prepared proof account follows the real-projective antipodal model:
matrix rank s+1, sphere dimension 4s^2, diagonal witness
(1,-1/s,...,-1/s), and uniform tracial two-norm sqrt(1/s). Odd off-diagonal
coordinate maps have common zeros by Borsuk-Ulam; late-coordinate states
solve finite self-commutator constraints. Compactness yields a corona trace,
which gives a discontinuous completion trace through tail truncations.
The older informal complex-projective model uses a different witness and a
character; it is identified as an earlier argument rather than presented
as the architecture of the selected Lean proof.

Astra's original mathematical argument and the Claude/Codex development
roles are disclosed. The existing HamSandwich Borsuk-Ulam formalization is
credited separately as reused code, pinned to
`76202dbbb6610ffcebbccfbf7a56f833a4c2a376`; its port and Apache-2.0 provenance
are documented in `GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md`.
The upstream HamSandwich README's disclosed Aristotle (Harmonic) and
ChatGPT production roles are preserved separately from local automation
credits. No human expert review is claimed.

## Literature, credit, and earliest asking

The [comprehensive literature and credit audit](https://github.com/SauersML/group-approximation/blob/637ae0c8446d073e1e1000e54a924742cc6f7041/research/artifacts/stw-xxii-literature-and-credit-audit.md)
contains the primary-source bibliography, statement comparisons, proof
account, and precise limits of the priority finding. Its main corrections
are incorporated in the candidate metadata, not merely recorded here.

- **May 25, 2020:** Aaron Tikuisis publicly asks the exact trace question
  in the [Fields Institute talk](https://www.youtube.com/watch?v=qrtLAOC3ZIU&t=2260s),
  at 37:40–38:58. The [event record](https://www.fields.utoronto.ca/talks/PLENARY-Uniformly-tracially-complete-C-algebras)
  fixes the date and speaker. The video was uploaded June 4, 2020;
  its description's unrelated Quantum Graphs title is a metadata error.
  This credits Tikuisis as the presenter, not as sole originator.
- **October 31, 2023:** the earliest verified paper formulation is
  [CCEGSTW v1, Question 1.1, p. 9](https://arxiv.org/pdf/2310.20594v1),
  with collective credit to Carrión, Castillejos, Evington, Gabe,
  Schafhauser, Tikuisis, and White.
- **June 12, 2025:** [STW v1](https://arxiv.org/pdf/2506.10902v1) already
  contains Problem XXII; the statement citation pins v2, May 8, 2026.
- The classical obstruction receives explicit credit to
  [Pedersen–Petersen](https://doi.org/10.7146/math.scand.a-10998),
  [Bice–Farah](https://arxiv.org/abs/1307.0111), and
  [Robert](https://arxiv.org/abs/1309.0498).
  [Ozawa](https://arxiv.org/abs/1304.3523) receives foundational
  completion credit. The claim is an original counterexample application.
- [Vaccaro's earlier nonfactorial ultraproduct](https://arxiv.org/abs/2303.01942)
  is distinguished from a counterexample satisfying factoriality.
  The cited positive results preserve the type II₁ hypothesis for the
  general CPoU theorem and triviality for the Farah–Vaccaro bundle theorem.

An additional backward check read Evington's public
[2015 slides](https://drive.google.com/open?id=1mW_uTdo_-EZBymR0peKUyYQ8H1CA9U0X)
and [2016 slides](https://drive.google.com/open?id=124OjT_oOFKBgDupju2QobbHCU921tYJm).
Their explicit Ozawa-attributed question concerns bundle triviality over
infinite-dimensional bases, not the selected trace question; they do not
move the earliest explicit asking established by the 2020 recording.

No earlier solution of the exact selected question was located in the
primary literature examined through September 14, 2026 UTC. This is not
an absolute-priority certification. The supplied transcript is identified
as such; its permalink, upload-date discrepancy, and matching official
event record are documented, without claiming independent audio transcription.

## Policy checked

- PalomarPolicy commit `e9c8c238f5695b10f75db7175648a1d0195352c1`:
  [CONTRIBUTING](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/CONTRIBUTING.md)
  and [specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/docs/specification.md).
- Metadata schema repository commit `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`, v0.4.
- [Agent intake instructions](https://submit.palomar-registry.org/llms.txt), read only.

The user authorized preparation and explicitly prohibited submission.
No intake POST, verification challenge, gist, submission, or registration was
created. Before a future agent-driven intake, those instructions require the
user's agreement on the concrete repository, SHA, configuration and their
authorization relationship. The proposed relationship is `maintainer`.

## Prepared future intake body — not sent

```json
{
  "repository": "SauersML/group-approximation",
  "commit": "637ae0c8446d073e1e1000e54a924742cc6f7041",
  "comparator_config_path": "Palomar/comparator-stw-xxii.json",
  "authorization_relationship": "maintainer"
}
```

This record and [the submission guide](https://github.com/SauersML/group-approximation/blob/637ae0c8446d073e1e1000e54a924742cc6f7041/Palomar/STWProblemXXIISubmission.txt)
provide the values needed for a later submission. No access token or pending
intake secret exists for this prepared package.

## Candidate source hashes

| Candidate file | SHA-256 |
|---|---|
| `formalization.yaml` | `b947daf1e0211a8c16b06038208504e3acfdc08b99822ee4f0444a56f4d84337` |
| `metadata/palomar-stw-xxii.yaml` | `b947daf1e0211a8c16b06038208504e3acfdc08b99822ee4f0444a56f4d84337` |
| `Palomar/comparator-stw-xxii.json` | `6f17c3a47ce5a37819ef3335f6f4752890b533adad35bf89bd309b309bc020e7` |
| `Palomar/STWProblemXXIIChallenge.lean` | `c74406f42522de13b144c8313bb3e0cccfccef63850924c9c967838f8cec87f1` |
| `Palomar/STWProblemXXIISolution.lean` | `d099caf7367418e27bcdec0ffe87c5e5dde74506139c90d552e2ae69bac14fcc` |
| `lean-toolchain` | `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e` |
| `lake-manifest.json` | `d52fe29fe16fa16b8765f1d0a085f2c66a8fcc7343d9e82e39cb4222603169e0` |
| `research/artifacts/stw-xxii-literature-and-credit-audit.md` | `3abaf75432500df2c56b64fe3f62e00f7f695a3deeba8dc1605796064734e50d` |
| `GroupApproximation/ThirdParty/HamSandwich/UPSTREAM.md` | `ae92f58c892eb0963617daae488324dbb71f16950bc21de02cc3472ee8157be2` |
