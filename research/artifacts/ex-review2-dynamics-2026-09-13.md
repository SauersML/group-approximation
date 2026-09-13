# EX review 2: dynamics, entropy and HS stability (2026-09-13)

Lane `ex-verify2-dynamics` (EX swarm), second-wave adversarial verifier. Start tip `7d41d1a16`.

First-wave reviews of these lanes:
- `ex-review-dynamics-2026-09-12.md` and parts 1–3;
- for the HS lane, `ex-review-backlog-2026-09-13.md`, parts 5–7 (§§11, 20, 30, 33).

## 0. Scope and method

**Lanes.**
- ex-bernoulli-rokhlin-complete, ex-bernoulli-zero-supremum, ex-bernoulli-positive;
- ex-rokhlin-ascent-finite-kernel, ex-rokhlin-ascent-joint-counting, ex-rokhlin-lower;
- ex-nonsofic-action-entropy, ex-sl3z-cocompact-quotient, ex-tree-lattice-mixing;
- ex-hs-instability-kazhdan.

**Verdicts.**
- **PASS.** The claim was re-derived independently, and the statement, hypotheses and citations match.
- **GAP.** The statement may be true, but the written argument or its scope does not prove it as stated.
- **FAIL.** The statement is false as written, or the argument is broken beyond local repair. A wording
  FAIL with a one-line fix is labelled as such and corrected forward.

**Status.** Established, open and refuted were recomputed at `7d41d1a16` by a route fixpoint over the
frontmatter of every `research/*.md`.
- A route fires when three conditions hold: its target is not refuted; every requirement is established
  and not refuted; and no established claim invalidates it.
- Graph-wide totals: 10,099 claims (8,359 established, 1,548 open, 192 refuted) and 435 dead routes.
- This is a reader's recomputation, not `cairn check`.

**PASS rows.** A claim counts as passed when some row of an `ex-review-*.md` file names it in backticks
with a PASS verdict.

## 1. Census

**Landings.**

| lane | commits |
|---|---|
| ex-bernoulli-positive | 26c156968e, 781800afec, 433c5db36c, a1e1bf7e3c, 9c34e9e7f5, 8e8c53cea1 |
| ex-nonsofic-action-entropy | 3ecde705af, 577c3a94cd, d7a988a3fc, 2739e2b19a, b7acd41a75, 55c6f92ac7, cd3a1a5c40, 18dddf7c58, 8b13935ba6 |
| ex-rokhlin-lower | a564fb2cfc, 142d6e141e, eed9297d75, aa3a1af8ca, 5cfbc66cc5, 16138868dd |
| ex-tree-lattice-mixing | 4c5d1a7d34, 4581f9bd74, ec264e8a32, b0b785ed38, 79102e615f, aafc5e8540, c267237d8b, 346bf1adb2, 4f039a7801 |
| ex-bernoulli-zero-supremum | e619b92974, b38ee6bf9a, 0bb801a234, cce47a6658, a64112c960, cdabc1905f |
| ex-bernoulli-rokhlin-complete | a091c1f300, 71a738c65d, 28228d886b |
| ex-rokhlin-ascent-joint-counting | 072ee83b19 |
| ex-rokhlin-ascent-finite-kernel | d89291ca28, e499fdc3e3, ac683b428b, a6e97fbd26, 4a097a5f45 |
| ex-hs-instability-kazhdan | 3d19cd88eb, a52bf65b6f, a36fec7696, e93af47046, 781c47abf0, 3689daa16b, bcd399dfb5, b08827ebd2 |
| ex-sl3z-cocompact-quotient | 5dea6f786f, a5893bd6f5, 4301977864, e48aab9bfa, 324b0eede3, 9544c83e55 |

**Counts.** These pushes contain 96 claim files, including peers' claims that the lanes edited.
- At `7d41d1a16`: 61 established, 35 open, 0 refuted.
- Of the 61 established claims, 45 have a PASS row and 16 have none.

### 1.1 Established, with no PASS row (16)

| lane | claim | type | first-wave note |
|---|---|---|---|
| hs-instability-kazhdan | `bdhv-central-extension-property-t` | import | backlog §11.2: consistent, not re-read |
| nonsofic-action-entropy | `cordeiro-sofic-relation-permanence` | import | none |
| nonsofic-action-entropy | `paunescu-sofic-action-class-permanence` | import | none |
| nonsofic-action-entropy | `popa-bernoulli-cocycle-superrigidity` | import | none |
| nonsofic-action-entropy | `popa-oe-superrigidity` | import | source checked (dynamics part 2 §13e), id not named |
| rokhlin-lower | `alpeev-seward-stabilizer-growth-kills-outer-entropy` | import | source checked (§13e), id not named |
| sl3z-cocompact-quotient | `benoist-quint-zariski-dense-invariant-measures-are-haar` | import | none |
| sl3z-cocompact-quotient | `bms-sln-z-representations-agree-with-algebraic-ones` | import | none |
| sl3z-cocompact-quotient | `sl3z-cocompact-quotient-uniquely-ergodic-minimal` | proof | none |
| sl3z-cocompact-quotient | `uniquely-ergodic-action-sofic-iff-topological-microstates` | proof | none |
| sl3z-cocompact-quotient | `sl3-norm-drift-excludes-finite-almost-invariant-configs` | proof | none |
| sl3z-cocompact-quotient | `sl3z-cocompact-microstates-carry-flat-lambda-labels` | proof | none |
| sl3z-cocompact-quotient | `sl3z-cocompact-quotient-uniformly-far-from-finite-actions` | proof | none |
| sl3z-cocompact-quotient | `hecke-orbits-make-lattice-quotient-actions-sofic` | proof | none |
| tree-lattice-mixing | `burger-mozes-infinitely-transitive-tree-groups` | import | §13e: items 1–3 read, items 4–5 not |
| tree-lattice-mixing | `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups` | proof | none |

### 1.2 Established, with only a partial PASS (second-pass targets)

| claim | what the first wave left |
|---|---|
| `flexible-hs-stability-descends-to-retracts-finite-index` | "PASS at the checked steps"; the final comparison (§5 of the route) was not read |
| `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` | the corollary (§5 of the route) was not read line by line |
| `sl3-polynomial-congruence-subgroups-have-large-b2` | "PASS as a conditional"; the table was not re-derived |
| `radu-horizontal-projection-kills-delta-squared` | named only as an input that was not re-derived |
| `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex` | owner ex-q34-kt-double; "PASS as an implication" |

### 1.3 Open claims touched (35); none decides a famous problem

- **Famous-level targets, all OPEN.**
  - `sl3z-on-cocompact-lattice-quotient-is-not-sofic`, `sl3z-admits-nonsofic-action`,
    `mixing-free-nonsofic-action-of-sofic-group` and `simple-group-lattice-admits-nonsofic-action`.
  - `radu-bmw-lattice-sofic` and `radu-bmw-lattice-nonsofic`.
  - `el-r-polynomial-vertex-not-flexibly-hs-stable` and `hs-stable-vertex-rounding-for-every-model`.
  - `every-group-has-positive-rokhlin-entropy-action` and `zero-rokhlin-supremum-forces-bernoulli-collapse`.
- **Bernoulli bridges, OPEN.** `iid-generators-dense-at-zero-rokhlin-supremum`,
  `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`, `bernoulli-shift-entropy-classifies-for-every-group`
  and `thompson-v-bernoulli-measure-finitely-determined`.
- **Premises and approximations, OPEN.**
  - SL_3 lane: `sl3z-cocompact-quotient-admits-no-topological-microstates`,
    `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions` and `sl3z-is-stable-in-finite-actions`.
  - HS lane: `sl3-polynomial-covers-have-extra-finite-quotients`,
    `sl3-polynomial-finite-index-z-extension-center-survives` and `flexibly-but-not-strictly-hs-stable-group-exists`.
  - Tree lattices: `radu-nilpotent-by-arithmetic-quotients-are-sofic`, `non-rf-tree-lattices-are-lifts-of-arithmetic-lattices`,
    `nonsofic-infinitely-transitive-tree-lattice`, `nonsofic-one-vertex-square-complex-group`,
    `radu-bmw-lattice-embeds-in-infinitely-transitive-tree-lattice`, `f2xf2-admits-mixing-nonsofic-action`,
    `f2xf2-admits-nonsofic-action`, `f2xf2-in-paunescu-class` and `nonsofic-lattice-with-dense-projections-in-tree-product`.
  - Rokhlin entropy: `rokhlin-maximality-ascends-finite-normal-extensions`,
    `rokhlin-maximality-ascends-amenable-normal-extensions`, `kun-thom-wreath-bernoulli-rokhlin-maximal`,
    `seward-direct-product-relative-rokhlin-entropy-conjecture`,
    `weakly-bernoulli-liftable-actions-force-virtual-splitting` and `deligne-triple-cover-surjunctive`.

### 1.4 Dead routes

Each of the three `requires: []` routes into an open target is invalidated by an established obstruction that
has a PASS row.

| dead route | invalidator | PASS |
|---|---|---|
| `mixing-nonsofic-action-via-soe-from-kun-thom-action` | `kun-thom-action-soe-class-is-rigid` | dynamics part 2 §9 |
| `mixing-nonsofic-action-via-weak-containment-of-kun-thom-action` | `weak-containment-is-blind-to-kazhdan-fixed-algebras` | part 1 §3 |
| `amenable-kernel-ascent-via-coherent-kernel-windows` | `coherent-kernel-folner-windows-force-conjugation-invariant-mean` | part 2 §10 |

No other route of these lanes fires into an open or famous target. Conditional routes stay unfired while
their premises are open.

## 2. Part files

- **Part 1.** ex-hs-instability-kazhdan: second pass on (T), rounding, descent, the b_2 table, and the BdHV
  import.
- **Part 2.** ex-sl3z-cocompact-quotient: unique ergodicity, the microstate criterion, norm drift, flat labels,
  the uniform exclusion, Hecke orbits, and the Benoist–Quint and BMS imports.
- **Part 3.** Tree lattices (Radu's lattice as a limit of nilpotent-by-arithmetic groups) and the remaining
  imports (Cordeiro, Păunescu, Popa, Burger–Mozes items 4–5).
- **Part 4.** Bernoulli bridge nodes (`generators-dense-iff-zero-rokhlin-entropy` and its bridges).

Verdicts are recorded in the parts and summarized here as they land.
