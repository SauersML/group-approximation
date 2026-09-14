# Fake surfaces of small complexity: census recount and stable Andrews–Curtis certificates (2026-09-14)

Lane `hl-andrews-curtis`, second pass. Earlier status pins:
`research/artifacts/hl-andrews-curtis-status-2026-09-13.md`.
Code: `experiments/andrews-curtis-fake-surfaces/`.
MSI working directory: `/scratch.global/sauer354/hl-andrews-curtis/fs/`.

## 1. The handle

L. Fagan, Y. Qiu, Z. Wang, *Stable Andrews–Curtis conjecture via fake surfaces and
Zeeman conjecture*, arXiv:2412.12293v2 (8 Jan 2026), `main.tex`:
- l.277–279 (Theorem `thm:main`): "Contractible fake surfaces of complexity less than
  6 with connected 1-skeletons are all 3-deformable to a point."
- l.329: "sACC is also equivalent to the conjecture that every contractible fake
  surface 3-deforms to a point."
- l.2075: "Using the classification of contractible fake surfaces up to complexity 5
  from \cite{fagan2024classification}, it is easy to check that all satisfy one of the
  conditions of Lemma~\ref{lem:crl}."
- l.2147: "While computer exploration has not yielded any new results so far, we plan
  to continue this approach in the future."

The classification is L. Fagan, Y. Qiu, Z. Wang, *Classification of Cellular Fake
Surfaces*, arXiv:2406.09439v3 (8 Jan 2026). Its data are `fakesurfaces.csv` in
github.com/lucasfagan/Fake-Surfaces (commit 7bcff60, 2024-06-18).
- The table at l.366–385 gives 2, 17, 238, 4618 contractible surfaces of complexity
  1–4.
- l.589–591: complexity 5 is classified only "in the case of no disks of boundary
  length 1 and 2".

So stable AC is pinned for complexity ≤ 5 only through a finite list, and complexity
6 is open.

## 2. Model

A cellular fake surface of complexity t is determined by two pieces of data:
- **Singular graph.** A connected 4-regular multigraph Γ with t vertices and 2t edges.
- **Edge matchings.** For each edge, a bijection between the three sheets at its two
  ends.

At a vertex the six sheet corners are the six pairs of half-edges. Corner walks give
the disk boundaries. Homeomorphism classes are orbits of the half-edge automorphism
group of Γ. The full argument is in `fake-surface-census-recount-proof`.

Code: `fsenum.cpp` (C++/OpenMP) enumerates and canonicalizes; `fsac.py` is a second,
independent Python model.

## 3. Recount against the published census

| t | graphs | acyclic classes (recount) | published | missing | no small disks (recount / published) |
|---|---|---|---|---|---|
| 1 | 1 | 2 | 2 | 0 | 0 / – |
| 2 | 2 | 17 | 17 | 0 | 0 / – |
| 3 | 4 | 239 | 238 | 1 | 2 / – |
| 4 | 10 | 4676 | 4618 | 58 | 31 / – |
| 5 | 28 | 111,460 | – | – | 517 / 514 |

Checks behind the table:
- **Orbit–stabilizer** passes on every graph (MSI job 779877).
- **Automorphism counts.** An independent brute force (`autcheck.py`) gives the same
  |Aut| on every graph with t ≤ 4.
- **Second implementation.** The Python model agrees on disks, disk lengths and
  determinants for all 116,394 classes.
- **Match against the census** (`diag2.py`). Every published row maps to a distinct
  recount class, and no row is unmappable.
- **Where the missing classes sit.** They lie in graphs with parallel edges. At t = 4:
  graph 3 has 36, graph 5 has 11, graph 8 has 6, graph 7 has 4, graph 6 has 1.

## 4. The defect in the published duplicate removal

`fakesurfaces_cla_6.py`, `are_compatible` and `are_same_with_ordering`, grow a
dictionary of signed letters `d[disk1[i]] = disk2[...]`. The dictionary never
requires `d[-x] == -d[x]`.

Example: complexity 3, graph 3 (vertex list `[0,0,0,1,0,2,1,2,1,2,1,2]`: a loop, two
single edges, a triple edge).
- Code 435: `[1,2,5,-3,-1,2,4,-5,4,-3,1], [2,6,-3], [4,-6], [5,-6]`.
- Code 477: `[1,2,6,-3,-1,2,4,-5,4,-3,1], [2,5,-3], [4,-6], [5,-6]`.

`are_same` returns True through 16 letter maps. Each contains 5 ↦ 6, −5 ↦ −5, 4 ↦ 4
and −4 ↦ −6. A brute force over all 24 edge-preserving half-edge bijections of this
graph finds no isomorphism 435 → 477 (`samecheck2.py`).

## 5. Certificates

**Presentation.** P(F, T) takes the non-tree edges as generators and the disk words
as relators. A certificate is a list of macros `conj`, `inv`, `mulc`, `destab`, each a
composite of (AC1)–(AC5). Replay must end with the empty presentation.

**Search and check.**
- **Producers:** `fsac.py` modes `certify`, `rescue` (all spanning trees; A₅ images),
  `rescue2` (backtracking, bounded product BFS, coset enumeration).
- **Checker:** `acverify.py` is standalone. It rebuilds the relators from
  (graph, code, tree), checks det ±1, and replays.
- **Join:** `coverage.py` joins class lists with checked records.

**Results for t ≤ 5.**
- t = 1, 2, 3: every class certified on the first pass.
- t = 4: 4664 on the first pass, 12 on another tree.
- t = 5:
  - 111,067 on the first pass;
  - 389 on another tree;
  - 1 by backtracking;
  - 2 by the product BFS, after coset enumeration showed their groups trivial;
  - 1 class (graph 28, code 37967319) with a nontrivial A₅ image, so π₁ ≠ 1.

**Coverage** (MSI job 785019, `coverage.py`, every record re-checked by `acverify.check`): 0 uncovered classes.

| t | classes | stably AC-trivial | π₁ nontrivial |
|---|---|---|---|
| 1 | 2 | 2 | 0 |
| 2 | 17 | 17 | 0 |
| 3 | 239 | 239 | 0 |
| 4 | 4676 | 4676 | 0 |
| 5 | 111,460 | 111,459 | 1 |

## 6. What is and is not claimed

**Claimed.**
- `fake-surface-census-misses-acyclic-classes`: the published list misses 1 / 58 / 3
  classes.
- `fake-surfaces-up-to-complexity-five-are-stably-ac-trivial`: every contractible
  cellular fake surface of complexity ≤ 5 has a stably AC-trivial presentation.

**Not claimed.**
- No refutation of either Fagan–Qiu–Wang theorem, only a hole in the printed
  verification.
- The topological 3-deformation statement is imported through Wright (1975); the
  primary source was not read.
- Nothing about AK(3): its fake surfaces have higher complexity, which was not
  computed.

## 7. Complexity 6 and reproduction

- **Complexity 6 enumeration.** 97 graphs; job 780533, 48 threads, 48:40 wall.
  - 2,967,338 acyclic classes, 7762 of them without small disks.
  - The t = 3, 4, 5 regression reruns matched byte for byte.
- **Complexity 6 certification.** Job 788925 ran certify → rescue → rescue2 → acverify
  → coverage.
  - First pass: 2,952,729 certified, 14,609 stuck, 0 model disagreements.
  - Rescue: 14,426 on another tree, 5 with an A₅ image, 178 open.
  - Rescue2: all 178 by backtracking with the product search.
  - Standalone `acverify`: 2,967,333 stably AC-trivial, 5 π₁-nontrivial, 0 failures.
  - Coverage: 0 uncovered.
- **π₁-nontrivial classes at t = 6** (graph, code): (78, 1366823383), (88, 704843050),
  (95, 520477952), (95, 1366799766), (97, 748582661).
- **Claim:** `fake-surfaces-of-complexity-six-are-stably-ac-trivial`.
- **Discarded run.** Job 785018 wrote truncated gzip shards and is discarded: the
  producer did not close its streams, fixed in c4df83a50.
- **Jobs.**
  - calibration 779877;
  - certification 780529;
  - rescue 781551;
  - standalone verification 784298;
  - coverage 785019.
  - `rescue2`/`rescue3` for the 3 open t = 5 classes ran on the login node:
    `rescue2-t5.jsonl`, `rescue3-t5.jsonl`.
