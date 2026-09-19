# Solver-free census re-check (w12-107, 2026-09-18)

This directory holds one fresh script, `recheck.py`, that re-verifies every solver-free certificate
for the BMW census in degrees (3,3), (4,3), (4,4) and (5,3). It also checks that together they cover
every class that is not certified reducible.

`recheck.py` was written from the certificate formats alone. It shares no code with the search or
checking scripts of the lanes that produced the certificates (w6c, w7, w8, w9, w10, w11). It imports
only the Python standard library and uses no SAT solver.

## Inputs

It reads the 20 census files `experiments/bmw-census-left-orders-2026-09-17/census_<pat>.json` and the
pipeline's `out_<pat>.jsonl`, which it uses only as a cross-check of finiteness. It also reads these
certificate files:

| source | format | lane |
|---|---|---|
| `bmw-klein-chains-2026-09-17/chains_*.json` | Klein chains | w6c (and `bmw-40-40-193-281-332-klein-chain-proof`) |
| `bmw-klein-chains-transposed-2026-09-17/chains_*.json` | Klein-power chains with roots | w7 |
| `bmw-klein-frames-2026-09-18/chains_*.json` | frame chains | w8 |
| `bmw-klein-free-2026-09-18/tree_*.json` | cone trees (last JSON line) | w9 |
| `bmw-cone-trees-2026-09-18/trees.jsonl.gz` | cone trees | w10 |
| `bmw-short4-cone-trees-2026-09-18/certs.jsonl.gz` | cone lemmas | w11 |

## What is checked

The soundness arguments are in `research/bmw-census-solver-free-parity-kernel-certificates-proof.md`.

- **Per class:**
  - the squares form a bijection and the inverse maps are involutions;
  - both critical-overlap families of the rewriting system resolve (confluence);
  - two independent normal-form algorithms agree on 60 random words.
- **Chains:** every element is nontrivial with even `v`- and `h`-lengths. Every step is (K)
  `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}`, or (R) `x_i = r^e`, `x_{i+1} = r^f` with `1 ≤ |e| < |f|`.
  At least one step is (K).
- **Trees:** every split element lies in `Γ^+ − {1}`. Every leaf step multiplies two elements already
  in the set. Every leaf ends with `xy = 1`.
- **Cone lemmas:** every table entry lies in `Γ^+ − {1}`. The steps are products, squares, or citations
  of earlier lemmas with exactly one element outside the set. Each lemma ends in a contradiction, and
  the last lemma is empty.
- **Coverage:**
  - `finite_order` computes the automaton images with cap 4000, and they must agree with
    `out_*.jsonl`;
  - every class that is not certified reducible must have a checked certificate;
  - uncovered classes are retried at cap 60000.

`mutate.py` applies 18 corruptions of the four certificate types. All are rejected (`mutate.log`).

## Runs

The certificate phase takes about 5 minutes, and the coverage phase runs one pattern after another.
To stay within the 1200 s limit on a loaded machine, the work was split into parts, all collected in
`recheck.log`:
- **Part 1:** a full run that covered the (3,3) and (4,3) patterns before a container restart
  stopped it.
- **Parts 2–5:** full runs, each restricted to some patterns with `RECHECK_PATS=<p1,p2,...>`.
- **Part 6:** a coverage-only rerun of `51_30` with `RECHECK_OKLOG=<log>`, which takes the checked
  set from an earlier full log.

Every full run re-checked all certificates. Its OK lines are byte-identical to part 1's.

`RECHECK_PATS`, `RECHECK_OKLOG` and the cap-60000 second pass for uncovered classes were added to
`recheck.py` between runs. The checkers themselves did not change.

## Result

**Result** (`recheck.log`):
- **Certificates:** 1206 certificates on 1203 classes checked, 0 rejected. Three classes have two
  certificates: `40_40` #193, #281 and #332.
- **Census:** 6964 classes. At cap 4000, 5763 are certified reducible. `51_30#506` is also certified
  reducible at cap 60000, with image orders 6 and 6912, as in `bigcap.log`.
- **Candidates:** 1200, and all 1200 have a checked certificate. The other 3 certified classes are
  reducible Promislow-type classes (`41_40` #1174, `41_41` #486 and #541).

| degree | patterns | classes | certified reducible | candidates | covered |
|---|---|---|---|---|---|
| (3,3) | 30_30, 31_30, 31_31 | 60 | 56 | 4 | 4 |
| (4,3) | 40_30, 41_30, 41_31, 42_30, 42_31 | 639 | 589 | 50 | 50 |
| (4,4) | 40_40, 41_40, 41_41, 42_40, 42_41, 42_42 | 3822 | 3133 | 689 | 689 |
| (5,3) | 50_30, 50_31, 51_30, 51_31, 52_30, 52_31 | 2443 | 1986 | 457 | 457 |
| total | 20 | 6964 | 5764 | 1200 | 1200 |

The candidate counts agree with the census claims:
- 62 for (3,3), (4,3) and `42_42` (`small-degree-irreducible-bmw-parity-kernels-not-left-orderable`);
- 301 for `40_40`, which includes #193, #281 and #332;
- 190 for `50_30`.

The certificates come from these families:

| family | classes |
|---|---|
| Klein chains (w6c) | 33 |
| Klein-power chains (w7) | 171 |
| frame chains (w8) | 3 |
| quaternionic cone trees (w9) | 2 |
| cone trees (w10) | 485 |
| cone lemmas (w11) | 509 |

## Reproduce

    cd experiments/bmw-census-solver-free-recheck-2026-09-18
    python3 recheck.py ../..                       # all patterns (about 1 h single-threaded)
    RECHECK_PATS=40_40 python3 recheck.py ../..    # one pattern
    python3 mutate.py ../..
