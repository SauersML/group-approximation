# BMW census: parity-kernel left orders

This directory backs `research/small-degree-irreducible-bmw-parity-kernels-not-left-orderable.md`. The proof route
is `research/small-degree-bmw-parity-kernels-not-left-orderable-proof.md`.

Requirements: Python 3 and `python-sat` (CaDiCaL 1.5.3 and Glucose 4). Every run is single-threaded.

## Pipeline

1. Enumerate the complexes and write `census_{m}{pA}_{n}{pB}.json`, the class representatives up to relabelling,
   reversal and swap. Here `pA` and `pB` count transposed letter pairs; the other letters are involutions.

   ```sh
   python3 vh_enum.py m pA n pB
   ```

2. Check the enumerator against brute force over all 9! bijections in degree (3,3):

   ```sh
   python3 crosscheck_33.py
   ```

3. Run the pipeline in chunks of 100 classes under `nice -n 10 timeout 1200`:

   ```sh
   sh run_all.sh
   ```

   Each class runs `python3 lo_census.py census_X.json lo hi`, which does the following:
   - checks confluence of the complete rewriting system;
   - certifies whether each automaton image is finite (`finH`, `finV`);
   - runs positive-cone ball-SAT on the parity kernel. Radius 4 with all products is always run. If an image is
     not certified finite, it continues with radius 6 (one factor of length at most 4), radius 6 (all products)
     and radius 8 (one factor of length at most 2), stopping at the first UNSAT.

   The results go to `out_X.jsonl`, one JSON record per class.

4. Check the fast multiplication against the rewriting normal form:

   ```sh
   python3 selfcheck.py census_*.json
   ```

5. Tabulate the outcomes:

   ```sh
   python3 summarize.py
   ```

6. Locate Radu's (3,3) complex and Janzen–Wise in the census:

   ```sh
   python3 identify.py
   ```

`mus.py` extracts a deletion-minimal unsatisfiable core. Complex 16 of `30_30` at radius 4 gives a core of 59
product triples.

## Results for the landed patterns

Every class is either certified reducible (both images finite) or has an UNSAT positive-cone instance for `Γ^+`.
No irreducible candidate is SAT.

| pattern | classes | reducible, R4 SAT | reducible, R4 UNSAT | candidates, UNSAT at R4 | candidates, UNSAT at R6 (short 4) |
|---|---|---|---|---|---|
| 30_30 | 20 | 18 | 0 | 1 | 1 (Radu, #10) |
| 31_30 | 27 | 26 | 0 | 1 | 0 |
| 31_31 | 13 | 12 | 0 | 1 | 0 |
| 40_30 | 164 | 137 | 0 | 8 | 19 |
| 41_30 | 173 | 160 | 1 (#172) | 5 | 7 |
| 41_31 | 116 | 108 | 1 (#107) | 4 | 3 |
| 42_30 | 105 | 103 | 0 | 2 | 0 |
| 42_31 | 81 | 79 | 0 | 2 | 0 |
| 42_42 | 118 | 110 | 0 | 8 (Janzen–Wise, #98) | 0 |

## Four-vertex complexes (minimal-covolume torsion-free lattices)

This part backs `research/minimal-torsion-free-small-tree-lattices-not-left-orderable.md`. Its proof route is
`research/minimal-torsion-free-small-tree-lattices-not-lo-proof.md`.

It covers torsion-free type-preserving lattices in `Aut(T_m) × Aut(T_n)` with four vertex orbits.

```sh
python3 cx4.py enum && python3 cx4.py run census_cx4_33.json 0 11 > out_cx4_33.jsonl   # degree (3,3)
python3 cxmn.py enum 3 4 && python3 cxmn.py run 3 4 0 98 > out_cx_34.jsonl         # degree (3,4)
python3 cxmn.py enum 3 3                                                            # census_cx_33.json
python3 crosscheck_cx.py      # backtracker = brute force; orbits partition the data
python3 summarize_cx.py       # tally; asserts every candidate stops UNSAT
python3 cx4_parity.py         # (3,3) BMW parity kernels -> four-vertex classes
python3 cxmn_parity.py        # (4,3) BMW parity kernels -> (3,4) four-vertex classes
```

| degree | classes | certified reducible | candidates | UNSAT at R4 | R6 (short 4) | R8 (short 2) |
|---|---|---|---|---|---|---|
| (3,3) | 11 | 9 | 2 | 1 | 1 (Radu, #6) | 0 |
| (3,4) | 98 | 64 | 34 | 13 | 20 | 1 (#72) |

## Degree (4,4) with involutions and degree (5,3)

This part backs `research/bmw-degree-44-53-parity-kernels-not-left-orderable.md` (proof route
`research/bmw-degree-44-53-parity-kernels-not-lo-proof.md`) and the OPEN
`research/bmw-44-sat-survivor-parity-kernels-not-left-orderable.md`.

```sh
for p in "4 0 4 0" "4 1 4 0" "4 1 4 1" "4 2 4 0" "4 2 4 1" "5 0 3 0" "5 0 3 1" "5 1 3 0" "5 1 3 1" "5 2 3 0" "5 2 3 1"; do
  python3 vh_enum.py $p; done            # census_*.json; enum_4040.log for 40_40
for f in census_4[0-2]_4[01].json census_5?_3?.json; do python3 selfcheck.py $f; done > selfcheck_2.log
sh run_all.sh; sh resume.sh              # (4,4); resume.sh also runs (5,3) (run_53.sh is the standalone form)
python3 summarize.py
```

Logs: `run_all.log`, `run_53.log` (`pattern start exit`). The stderr logs `err_*.log` were empty and are not
stored. Timed-out chunks were rerun: 40_40 #292–#299 per class (`rerun_40_40.log`, `rerun_40_40_tail.jsonl`),
50_30 #283–#299 and #481–#500 in chunks of 5 (`rerun_50_30.log`, `rerun_50_30.jsonl`), and merged into
`out_40_40.jsonl`, `out_50_30.jsonl`.

| pattern | classes | reducible, R4 SAT | reducible, R4 UNSAT | candidates UNSAT at R4 | R6 (short 4) | R8 (short 4) | open |
|---|---|---|---|---|---|---|---|
| 40_40 | 824 | 523 | 0 | 101 | 195 | 2 (#176, #256) | 3 (#193, #281, #332) |
| 41_40 | 1242 | 1017 | 3 | 96 | 126 | 0 | 0 |
| 41_41 | 544 | 480 | 4 | 27 | 33 | 0 | 0 |
| 42_40 | 543 | 491 | 0 | 31 | 21 | 0 | 0 |
| 42_41 | 551 | 505 | 0 | 28 | 18 | 0 | 0 |
| 50_30 | 604 | 414 | 0 | 54 | 134 | 2 (#258, #470) | 0 |
| 50_31 | 276 | 233 | 0 | 27 | 16 | 0 | 0 |
| 51_30 | 662 | 532 | 2 | 52 | 76 | 0 | 0 |
| 51_31 | 310 | 268 | 2 | 28 | 12 | 0 | 0 |
| 52_30 | 389 | 351 | 0 | 27 | 11 | 0 | 0 |
| 52_31 | 202 | 184 | 0 | 16 | 2 | 0 | 0 |

`51_30#506` is counted as reducible: `bigcap.py` at cap 60000 certifies both images finite (orders 6, 6912).

**Stragglers.**
- `bigsat.py census idx R short` builds the same CNF as `lo_census.lo_sat` but streams it into CaDiCaL 1.5.3 and
  Glucose 4 (`bigsat.log`, `bigsat256.log`, `bigsat5030.log` via `run_5030.sh`; radius 10 short 2:
  `bigsat10.log`, `bigsat193.log`).
- `bigcap.py census cap idx...` reruns `finite_image` with a larger cap (`bigcap.log`, `bigcap5030.log`).
- `localact.py r pattern...` tabulates local actions and the Thompson–Wielandt test (`irred_tw.py`) in
  `localact.log`.

**The three survivors (40_40 #193, #281, #332).** Irreducibility tools, all without a certificate so far:

| script | test |
|---|---|
| `irred.py`, `irred_kps.py`, `irred_q.py` (`irred_q.log`) | infinite-order element of `H_x` from a section equal or conjugate to `g^{±1}` |
| `halftree.py` | half-tree fixator certificate |
| `kernel.py` | lists short horizontal words acting trivially on `T_V` |
| `selfrep.py` | builds the invariant-subtree automaton group `K` (a quotient of `H_x`) and tests fractality |
| `klev.py` (`klev.log`, `klev193V.log`) | orders and derived series of `K` on levels 1–5 |
| `kkps.py`, `ksig.py` | orbit-signalizer infinite-order test on `K` |
| `kindex.py`, `kstab.py`, `kcoset.py` | index certificates `[K : φ_v(Stab_K(v))] < |Kv|` |
| `klt.py` (`klt.log`), `kltc.py` | level-transitivity chain `L_{i+1} ≤ φ_v(Stab_{L_i}(v))` with an exact closing edge |
| `l2rep.py` (`l2rep.log`) | exact self-replication of the stable chain group `L_2` of `#281`: 4 of 8 generators found |
| `abel.py` | `H_1(Γ^+)` by Reidemeister–Schreier and Smith form (`b_1 = 2`) |
| `morse.py` | Bestvina–Brady Morse-function pattern search (none) |
