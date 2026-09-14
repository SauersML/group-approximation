# Small-memory census of realizable strict pairs

Lane `hl-gottschalk-dynamics`, 2026-09-13. Scripts and outputs are in
`research/artifacts/gottschalk-small-memory-census-2026-09-13/`. All computation ran on MSI.

## 1. What is decided

By `surjunctivity-is-axiomatized-by-rectangle-clauses`, a group is not surjunctive iff it realizes
strict rectangle data `D = (mu, nu, T_f, T_r)`. The clause `rho_D` holds in every group iff it holds
in the forward-relation group `P(T_f) = < x_a | x_1 = 1, x_s x_m = x_s' x_m' along T_f >`.

For memories of sizes `|S| = ns` and `|M| = nm` (labels include `1`) and alphabet `A`:

    no group realizes strict data of shape (ns, nm) over A
      <=>  for every forward table T_f realized exactly by P(T_f) with distinct labels,
           and every rule mu with Dec(T_f), every decoder nu satisfies Enc(T_r^P),

where `T_r^P` is the reverse table realized in `P(T_f)`.

- *(=>)* A failure is strict data realized in `P(T_f)`.
- *(<=)* Strict data realized in a group `K` have a realized forward table `T`. The same data are
  realized in `P(T)`, whose realized forward table is `T` itself. `Dec` passes to `T` because it is
  coarser, and strictness at `K`'s reverse table implies strictness at the finer `T_r^P`.
- *Label collisions.* A realization with two equal labels, or a label equal to `1`, is the same
  automaton on a smaller memory, so it is covered by a smaller shape.
- *Independence.* Two cells in one row or one column never coincide, since their labels differ.
  So only rook-independent partitions of `S x M` occur.

## 2. Pipeline

1. `enum_tables.py`: every rook-independent partition of `S x M`, with its presentation `P(T_f)`.
   Shapes `2x2`, `2x3`, `3x2`, `3x3`: 4, 18, 18 and 588 tables.
2. `oracle.py`: the word problem among the `ns nm` forward words, the `ns nm` reverse words and the
   labels.
   - *Distinct:* exact permutation representations of degree at most 6 that satisfy every relator.
   - *Equal:* relator insertion and free reduction, searched from both ends.
3. `tietze.py` and `tietze2.py`: greedy Tietze elimination, then an exact decision in three cases.
   - Cyclic: exponent sums modulo the order.
   - Free: freely reduced words.
   - Free abelian of rank two: exponent vectors.

   Every other presentation is reported undecided.
4. `certify.py`: for every table Tietze leaves undecided, re-derives each oracle decision with a
   fresh seed.
   - *Equal pairs:* a replayed rewriting derivation, searched from both ends with maximal lengths 8
     then 10 and at most 2,000,000 nodes.
   - *Distinct pairs:* a re-evaluated permutation representation that satisfies every relator.
5. `census.py` (numpy) and `census2.py` (pure python, different encoding): for each closed table
   with distinct labels, every rule `mu`. Each finds the forced partial decoder when `Dec` holds,
   then tests every `T_r^P`-constant reverse assignment against every extension of the decoder on
   the tuples it reads.

## 3. Results

**Word problems.**

| shape | tables | Tietze cyclic | Tietze free | Tietze Z^2 | left to certificates |
|---|---|---|---|---|---|
| 2x2 | 4 | 3 | 1 | 0 | 0 |
| 2x3 | 18 | 8 | 7 | 0 | 3 |
| 3x2 | 18 | 8 | 7 | 0 | 3 |
| 3x3 | 588 | 291 | 115 | 6 | 176 |

- The Tietze decisions agree with the oracle on every table the oracle resolved: 4, 15, 15 and
  402 cross-checks, 0 mismatches.
- The first oracle pass left 10 tables of shape `3x3` unresolved: ids 76, 83, 227, 280, 305, 367,
  399, 410, 456 and 470. Each undecided pair was a commutation `x_s x_m` against `x_m x_s`, and all
  ten groups are cyclic (`Z/5` or `Z`), so Tietze decides them.
- The first certificate pass failed on 76 of 290 finished `3x3` tables. All 111 missing
  certificates were equalities, none separations; rewriting searches of length 10 hit their node cap.
  Of those tables, 56 are cyclic. The rerun certifies only the tables that Tietze does not decide.
- **Certificate rerun** (MSI job 751675, `run4.sbatch`; maximal lengths 8 then 10, both directions,
  2,000,000 nodes). It certified 3, 3 and 176 tables of shapes `2x3`, `3x2` and `3x3`, all 182 with
  0 failures (`cert4_*.out`).
- So every word-problem decision the censuses use is proven: exactly by Tietze, or by replayed
  derivations and re-evaluated permutation representations.

**Census over two symbols** (`census4_q2_*.out` for `census.py`, `census4b_q2_*.out` for `census2.py`):

| shape | closed tables | rules with `Dec` | strict data found |
|---|---|---|---|
| 2x2 | 4 | 12 | 0 |
| 2x3 | 18 | 56 | 0 |
| 3x2 | 18 | 56 | 0 |
| 3x3 | 384 | 1396 | 0 |

The two implementations agree on every count. The 204 non-closed `3x3` tables realize a coarser
table in their own group, which is already a closed table or a smaller shape.

**Conclusion.** Over two symbols, no strict pair with encoder and decoder memories of at most three
elements is realized in any group (`binary-strict-pairs-need-a-memory-with-four-elements`).

**Not covered.**
- Memories of size four or more.
- Alphabets with three or more symbols, except memories of size two. Those are already excluded for
  every alphabet by amenability of their cyclic memory groups.

**Consistency with `strict-left-inverse-memory-meets-memory-ratios`.** Its proof shows that a
table with a nontrivial rule satisfying `Dec` must join the identity row to another row.
`prefilter.py` finds nontrivial `Dec` rules on 2, 10, 10 and 404 tables of the four shapes, and
every one of them joins the identity row.

## 4. Reproduction

On MSI under `/scratch.global/sauer354/hl-gottschalk-dynamics/`, with `/usr/bin/python3.12` and a
venv holding numpy 2.5.3:

1. `python3 enum_tables.py <ns> <nm> tables_<ns>x<nm>.jsonl` for the four shapes.
2. `python3 oracle.py tables_<d>.jsonl oracle_<d>.jsonl 1` for each shape (job 739201).
   - That job ran revision md5 `d858610e`, which searches equalities from one end with maximal
     length 8. The landed revision `30c8f450` searches from both ends with maximal length 10.
   - The census uses only partitions proven by Tietze or by `certify.py`, so the revision does not
     change the result.
3. `sbatch run4.sbatch` (job 751675, 2026-09-14 00:36–00:45 CDT). Its log `run4.751675.log`
   records these md5s:

   | script | md5 |
   |---|---|
   | `oracle.py` | `30c8f450` |
   | `certify.py` | `7c5cd981` |
   | `tietze.py` | `39f1a2ac` |
   | `tietze2.py` | `977d57eb` |
   | `census.py` | `30575b63` |
   | `census2.py` | `4821c414` |
   | `enum_tables.py` | `bd32a62a` |

   Its outputs are `cert4_*.out`, `census4_q2_*.out` and `census4b_q2_*.out`. The same job writes the
   certificate records `cert4_*.jsonl` (about 1.4 MB), the partitions `oracle_*_v3.jsonl` that the
   censuses read, and the Tietze decisions `tietze2_*.jsonl`. All three sets are in this directory,
   so each certificate can be re-checked without rerunning the searches. `cert4_2x2_0.jsonl` is
   empty because Tietze decides every `2x2` table.
