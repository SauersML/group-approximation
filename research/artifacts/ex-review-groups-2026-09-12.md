# EX review: groups, dynamics, logic and L² lanes (2026-09-12)

Lane `ex-verify-groups`, adversarial verifier of the EX swarm. Working notes, one section per
checked claim or route. Long sections move to part files
`research/artifacts/ex-review-groups-2026-09-12-part<N>.md`, indexed at the end of this file.

## 0. Scope and method

Lanes under review: ex-q34-leavitt-hs, ex-q34-kt-double, ex-q34-collapse, ex-nh-fresh,
ex-fp-simple-sofic, ex-kazhdan-simple-hyperlinear, ex-left-orderable-nonsofic,
ex-thompson-v-soficity, ex-weak-soficity, ex-bernoulli-negative, ex-bernoulli-positive,
ex-rokhlin-lower, ex-nonsofic-action-relative, ex-nonsofic-action-entropy,
ex-determinant-monster, ex-lueck-approximation, ex-atiyah-torsion-free, ex-hyperbolic-vtf,
ex-complexity-sofic, ex-complexity-amenable, ex-free-bridges, ex-free-objects,
ex-free-unused-power, ex-free-unified-theory.

For every node those lanes land as ESTABLISHED, and for every reduction or equivalence route others
will build on, the argument is re-derived independently from the statement, and the statement is
checked against its sources. Each verdict is one of:

- **PASS**: the argument was re-derived; the statement, every hypothesis and every citation match.
- **FAIL**: the statement is false as written, or the argument has an error that is not repairable
  by a local fix. The owning lane is told, and the route is retired or the node corrected.
- **GAP**: the statement may be true but the written argument does not prove it (a missing step, a
  hidden hypothesis, a citation not checked against the source, a conditional stated as
  unconditional). The owning lane is told what closes it.

Priority: (1) anything that would decide a famous problem; (2) reductions others build on;
(3) the rest. Sweep criteria on every landed EX node: a `requires: []` route whose invalidator is not
itself established; prose saying "established" with no route into the claim; an id over 64
characters; a conditional result stated as unconditional.

## 0.1 Baseline: status of the roots these lanes target, before any EX landing

Read from `research/FRONTIER.md` at `ecea91ac0` (regenerated from `cairn check` at `3a4b43636`),
tip `fb6e743e6` at 21:36 CDT. These are the statuses as the graph reports them. None was re-derived
here; a later flip of any of them by an EX landing is a priority-(1) check.

Famous or high-impact roots, all OPEN at baseline:

| root id | statement | lanes |
|---|---|---|
| `q3-4-resolved` | Pestov Q3.4 either way | q34-* |
| `hyperlinear-nonsofic-group` | a hyperlinear nonsofic group | q34-leavitt-hs, q34-kt-double |
| `hyperlinear-implies-sofic` | hyperlinear implies sofic | q34-collapse |
| `non-hyperlinear-group` | an explicit non-hyperlinear group | nh-fresh |
| `infinite-simple-kazhdan-hyperlinear-group` | Pestov Open Question 9.1 | kazhdan-simple-hyperlinear |
| `hyperlinear-fp-infinite-simple-group` | a hyperlinear f.p. infinite simple group | fp-simple-sofic |
| `left-orderable-non-sofic-group` | a left-orderable nonsofic group | left-orderable-nonsofic |
| `thompson-v-hyperlinear` | Thompson's V is hyperlinear | thompson-v-soficity |
| `hyperlinear-nonsofic-from-thompson-v` | a hyperlinear nonsofic V answers Q3.4 | thompson-v-soficity |
| `bernoulli-shift-entropy-classifies-for-every-group` | Bernoulli classification over every group | bernoulli-* |
| `bernoulli-rokhlin-entropy-maximal-for-every-group` | maximal Bernoulli Rokhlin entropy | bernoulli-positive, rokhlin-lower |
| `every-group-has-positive-rokhlin-entropy-action` | positive Rokhlin entropy everywhere | rokhlin-lower |
| `hyperlinear-nonsofic-free-action` | a hyperlinear nonsofic free action | nonsofic-action-* |
| `sl3z-admits-nonsofic-action` | SL3(Z) has a nonsofic action | nonsofic-action-* |
| `mixing-free-nonsofic-action-of-sofic-group` | a mixing free nonsofic action of a sofic group | nonsofic-action-* |
| `determinant-conjecture-counterexample-exists` | a determinant conjecture failure | determinant-monster |
| `strong-atiyah-torsion-free` | Strong Atiyah, torsion-free | atiyah-torsion-free |
| `hyperbolic-groups-virtually-torsion-free` | hyperbolic groups virtually torsion-free, either way | hyperbolic-vtf |
| `nonsofic-hyperbolic-group` | a nonsofic hyperbolic group | hyperbolic-vtf |
| `sofic-recognition-finite-presentations-is-pi2-complete` | soficity of f.p. groups is Pi^0_2-complete | complexity-sofic |
| `amenability-of-finite-presentations-is-pi2-complete` | amenability of f.p. groups is Pi^0_2-complete | complexity-amenable |

No root for non-weakly-sofic groups or for the Lück approximation conjecture appears in FRONTIER at
baseline. Landings that create one are checked against the literature statement (Glebsky–Rivera and
Arzhantseva–Păunescu for weak soficity; Lück, Dodziuk–Linnell–Mathai–Schick–Yates and Jaikin-Zapirain
for approximation).

Established or refuted nodes at baseline that these lanes are likely to consume. They were not
re-derived here; a lane that builds a famous-problem route on one of them triggers a check of it:

- `openai-leavitt-unit-nonsofic` [ESTABLISHED]: `L_{F_2}(1,2)^x` is nonsofic.
- `finitely-presented-nonsofic-group-exists`, `fp-simple-nonsofic-group` [ESTABLISHED].
- `d-ary-leavitt-groups-nonsofic-over-finite-fields` [ESTABLISHED; Lean `Leavitt/AryEndpoints`].
- `sofic-groups-in-paunescu-sofic-action-class` [REFUTED], `commuting-sofic-actions-need-not-combine`,
  `coordinate-action-not-sofic`, `kt-free-action-hyperlinear-iff-wreath-hyperlinear` [ESTABLISHED].
- `bernoulli-rokhlin-maximality-passes-to-subgroups`, `bernoulli-rokhlin-deficit-has-a-finitary-witness`,
  `bijective-ca-preserve-uniform-bernoulli-measure` [ESTABLISHED].
- `determinant-conjecture-iff-serre-class-spectra`, `algebraic-atiyah-with-determinant-closed-under-colimits`,
  `algebraic-atiyah-and-determinant-one-group-tester` [ESTABLISHED].
- `fournier-facio-group-is-nonsofic` via `fournier-facio-nonsofic-citation` [ESTABLISHED].

One structural note from the baseline read: `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`
is OPEN and carries `refuted_by: [leavitt-units-have-zero-rokhlin-entropy-supremum]`. That claim's body
says OPEN, and none of its three routes (`leavitt-zero-rokhlin-supremum-from-strict-automaton`,
`leavitt-zero-supremum-via-measurable-compression`, `leavitt-zero-supremum-via-median-matching`) is a
`requires: []` route. A refuted_by edge from an open claim is not a refutation. An EX landing that
establishes the refuter is a priority-(1) check: `U` would then have zero Rokhlin entropy supremum,
which refutes maximal Bernoulli Rokhlin entropy over every group and positive Rokhlin entropy over
every group.

## Review sections

(None yet: no lane under review had landed at the time of this section.)

## Part files

(None yet.)
