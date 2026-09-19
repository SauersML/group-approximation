# Cone trees, quaternionic models and the A_5 parity test on the BMW census survivors

These are the artifacts of four nodes:
- `research/bmw-census-survivor-cone-tree-certificates.md`
- `research/bmw-quaternionic-type-53-parity-kernels.md`
- `research/bmw-quaternionic-char3-type-44-parity-kernels.md`
- `research/bmw-a5-parity-obstruction-to-pgl2-tree-models.md`

Each node has a `-proof.md` route. The census files are read from
`experiments/bmw-census-left-orders-2026-09-17/`; give them as bare file names. Run everything from
this directory. All runs are single-threaded, under `nice -n 10`.

## The remaining classes

`remaining.py` writes `remaining.json`: 994 classes in all, 470 first UNSAT at radius 4 and 524 first
UNSAT at radius 6 (short 4). A class is remaining when:
- it is a census class with `finH` or `finV` equal to `None` in `out_<pattern>.jsonl`, so its
  irreducibility is not certified;
- it has no Klein-power or Klein-frame certificate. The chains come from
  `experiments/bmw-klein-chains-2026-09-17` and `experiments/bmw-klein-chains-transposed-2026-09-17`,
  and five hand-entered classes from `bmw-klein-frame-chain-certificates` and
  `bmw-klein-free-quaternionic-parity-kernels`.

By degree there are 577 classes of `(4,4)`, 374 of `(5,3)`, 41 of `(4,3)` and 2 of `(3,3)`.

## Checkers (independent, exact; these carry the proofs)

- **`verify_cone.py census.json class tree.json`.** Checks one cone-propagation certificate. It uses
  only the census squares, its own rewriting normal form and a Newman critical-pair check. It is the
  checker of `experiments/bmw-klein-free-2026-09-18`, copied unchanged.
- **`verify_trees.py trees.jsonl.gz`.** Runs `verify_cone.py` on every record of the packed file.
  Output: `verify_trees.log`, whose last line is the summary.
- **`mutate_test.py trees.jsonl.gz`.** Shows that `verify_cone.py` accepts the `40_40` #818
  certificate and rejects four corruptions of it: a dropped step, a wrong product, a leaf without a
  contradiction, and a split on an element outside `Γ^+`. Output: `mutate_test.log`.
- **`verify_quat_rep2.py`.** Characteristic 2, sympy over GF(2), with its own structure constants for
  `[a, b)`. Covers the six `(5,3)` classes of family 53 in `[1, t+1)` and `30_30` #16 in
  `[t, t²+t+1)`. It checks:
  - associativity and the Gram determinant;
  - ramification at `b`;
  - all relations up to scalars;
  - the tree conditions (T1) and (T2).

  Output: `verify_quat_rep2.log`.
- **`verify_quat_rep3.py`.** Characteristic 3, sympy over GF(3). Covers every record with `found: true`
  in `quat3_44.jsonl` and `quat3b_44.jsonl` (nine classes of degree `(4,4)` in `(−1, t+1)`). Same checks as above. Output:
  `verify_quat_rep3.log`.
- **`parity5b.py`.** For every remaining `(5,3)` class, the sign and cycle type of each v-letter
  permutation `π_u`, read directly from the squares. It is compared with `parity5.json`. Output:
  `parity5b.json`, and the printed line `374 classes; 306 with an odd v-letter; agreement ... 374`.

## Search scripts (not needed for the proofs)

**Cone trees**
- `dtree2.py census.json class R maxleaves timeout [short]` is a lookahead DPLL tree finder on the
  radius-`R` ball (using `lo_census`). Its output format is the one `verify_cone.py` reads.
- `runall.py Rsel R maxleaves timeout log [patterns]` runs `dtree2.py` on every remaining class whose
  first UNSAT key is `Rsel`. It writes `trees/tree_<pattern>_<class>.json` and one log line per class.
  - `run_R4.jsonl` is `runall.py R4sNone 4 64 120 run_R4.jsonl`.
  - `run_R4b.jsonl` is `ONLY=run_R4.jsonl runall.py R4sNone 4 1500 900 run_R4b.jsonl`, which reruns
    the 59 failures with a larger budget; all succeed.
  - `run_R6.jsonl` is `runall.py R6s4 6 64 300 run_R6.jsonl`, continued with a 180 s timeout on the
    `(4,3)` and `(5,3)` patterns first.
  - `run_R6b.jsonl` is `ONLY=run_R6.jsonl runall.py R6s4 6 1500 400 run_R6b.jsonl 30_30 40_30 41_30`.
    It reruns the radius-6 failures of those patterns with a larger leaf budget.
  - In `run_R6.jsonl` the radius-6 ball of the `(4,4)` classes did not fit the budget. Their trees
    would need about 1.7 GB and more than 400 s each.
- `pack_trees.py trees trees.jsonl.gz` packs the trees into one gzipped JSON-lines file.

**Quaternionic models**
- `findquat.py census.json class d a b PV PH` (characteristic 2) uses `quat.py` and `gf2poly.py`.
  Polynomials are given as ints, where bit `i` is the coefficient of `t^i`.
  - `runquat2_53.sh` produced `quat2_53.out`: the ten `(5,3)` classes that pass the parity test and
    the heuristic filter.
  - `runquat2_53b.sh` produced `quat2_53b.out`: the other 58 classes that pass the parity test. It
    found nothing.
  - `quat2_30_10.out` is `findquat.py census_30_30.json 10 2 2 7 PV PH` for `(PV, PH) = (2, 3)` and
    `(3, 2)`: `30_30` #10 in `[t, t²+t+1)` with letters of degree at most 2. It found nothing.
- `findquat3.py census.json a b PV PH d classes...` (odd characteristic, `P=3` by default) uses
  `quatp.py` and `fpoly.py`. Polynomials are digit strings, lowest degree first. With `STRICT=1` it
  keeps only letters whose `Nrd` is supported on `PV`, `PH` and the ramified places.
  - `runquat3.sh` produced `quat3_44.jsonl`: the `(4,4)` classes passing the filter, in three
    algebras.
  - `runquat3b.sh` produced `quat3b_44.jsonl`: the filter-failing `(4,4)` classes, in `(−1, t+1)`,
    with 1200 s per pattern.
- `localfilter.py remaining.json localfilter.json` is the heuristic local-action filter (see the A_5
  node).
- `parity5.py` writes `parity5.json` and `parity5.log`.
