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
