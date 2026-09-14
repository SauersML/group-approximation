# SAT census of strict pairs: ternary 3x3 and binary 3x4, 4x3

Lane `gk3-strict-census-4`, 2026-09-14. Scripts are in `research/artifacts/gk3-strict-census-4-2026-09-14/`.
All computation ran on MSI under `/scratch.global/sauer354/gk3-strict-census-4/`.

A *strict pair* over a group `G` and alphabet `A` is an injective, non-surjective cellular automaton `tau`
with memory `M` and a left inverse `sigma` with memory `S` (both containing `1`, `sigma tau = id`).

## 1. Reduction

This is the reduction of `binary-strict-pairs-need-a-memory-with-four-elements`
(`research/artifacts/gottschalk-small-memory-census-2026-09-13.md`, section 1), which does not depend on the
alphabet. By `surjunctivity-is-axiomatized-by-rectangle-clauses`, `G` carries a strict pair of shape
`(|S|, |M|)` over `A` iff `G` realizes strict data `D = (mu, nu, T_f, T_r)` of that shape.

- If `K` realizes `D` with realized forward table `T`, the forward-relation group `P(T)` realizes the same
  data, and its realized forward table is `T` (the map `P(T) -> K` can only merge less).
- Its realized reverse table `T_r^P` is finer than `K`'s. `not Enc` passes to finer tables, so the data are
  strict at `(T, T_r^P)`.
- Equal labels give the same automaton on a smaller memory.

So no group carries a strict pair of shape `(ns, nm)` over `A` iff, for every forward table `T` on `S x M`
realized exactly by `P(T)` with distinct labels, the instance `Dec(T) and not Enc(T_r^P)` has no solution
`(mu, nu)` over `A`.

**Smaller shapes, for every alphabet.**
- A decoder memory of size at most two generates an amenable group
  (`amenable-decoder-memory-forces-surjectivity`).
- An encoder memory of size at most two generates a cyclic group; the automaton is surjective iff its
  restriction to that subgroup is, and cyclic groups are sofic, hence surjunctive.

## 2. Encodings

**Encoding A** (`satcensus.py`). One-hot variables for every entry of `mu: A^M -> A` and `nu: A^S -> A`.
- *Dec.* For every forward assignment `p` (deduplicated by its relay row indices and demand `p(1,1)`) and
  every relay output tuple `b` consistent with repeated rows: the clause `not(mu(row_k) = b_k for all k) or
  nu(b) = p(1,1)`. With exactly-one constraints, all clauses hold iff `Dec(T)` holds.
- *not Enc.* One-hot `y` on the reverse classes; at-most-one variables `z_m` and `w`; clauses
  `y(row m) = b and nu(b) = a -> z_m = a`, then `z = c and mu(c) = a -> w = a`, and `w != y(1,1)`. Since `y`
  and `nu` are total, `z_m` is forced to `nu(y(row m))` and `w` to `mu(z)`. So the clauses are satisfiable
  iff some `T_r`-constant `y` breaks `Enc`.
- Solver glucose 4 with DRUP proof logging. Every UNSAT proof is checked by `drat-trim`
  (github.com/marijnheule/drat-trim, `drat-trim.c` md5 `ef27987f`), and the CNF and proof are kept gzipped.

**Encoding B** (`satcensus2.py`), written separately: binary-coded symbols with invalid codes excluded; rules
keyed by symbol tuples; Dec imposed per forward assignment with no deduplication; pairs read and
deduplicated by separate code; solver CaDiCaL 1.9.5.

**Model check** (`checkmodel.py`): any satisfiable instance is re-evaluated directly on every `T_f`-constant
and `T_r`-constant assignment.

## 3. Calibration

On the certified realized tables of the binary census (`oracle_3x3_v3.jsonl`, md5 `fe00427d`):

| test | result |
|---|---|
| `strict`, q = 2, 3x3, encoding A | 384 closed realized pairs, 0 SAT, 384 UNSAT, 384 DRUP proofs VERIFIED |
| `strict`, q = 2, 3x3, encoding B | 384 pairs, 0 SAT, per-table agreement with A |
| `countdec`, q = 2, 3x3 | 1396 rules `mu` with `Dec`, the binary census's count |
| `planted` (discrete reverse table), q = 2 | A and B: 246 SAT, 138 UNSAT, per-table agreement; all 246 + 246 models pass `checkmodel.py` |

The planted instances drop the reverse relations. Those instances are satisfiable exactly when a nontrivial
`Dec` rule exists, so they exercise the not-Enc side of the encoding.

## 4. Ternary census, shape 3x3

RESULTS PENDING (MSI job 784115, `run_q3.sbatch`).

## 5. Binary census, shapes 3x4 and 4x3

**Enumeration** (`enum4.py`, MSI job 784124): partitions of `S x M` with at most one cell per row and column,
one representative per orbit of relabelings of the non-identity labels, with orbit sizes.

| shape | partitions | orbits | fail F1 | F3 | F4 | survivors (orbit mass) |
|---|---|---|---|---|---|---|
| 3x3 | 588 | 160 | 8 | 11 | 49 | 92 (340) |
| 3x4 | 30,240 | 2,591 | 17 | 152 | 406 | 2,016 (23,616) |
| 4x3 | 30,240 | 2,591 | 63 | 99 | 404 | 2,025 (23,754) |
| 4x4 | 17,427,192 | not enumerated | | | | |

Orbit masses add up to the partition counts. The filters exclude a table for every alphabet:
- **F1** (`strict-left-inverse-memory-meets-memory-ratios`): a strict pair needs some `s != 1` in `M M^-1`. At
  a realized table this is a block holding a cell of the identity row and a cell of another row.
- **F3** (`private-origin-rows-force-permutation-encoders`): the block of `(1,1)` is a singleton, and the
  origin blocks `(s,1)` avoid the identity row and meet other rows only along an acyclic order. Then every
  `Dec` rule is a symbol permutation.
- **F4**: the relator hypergraph (star spanning relators, identity letters deleted) peels to an empty
  2-core. Each peel eliminates a private generator by a Tietze move, so `P(T)` is free, hence sofic and
  surjunctive, and strict data at `T` would be realized in `P(T)`. This is the elementary part of
  `forward-relations-of-a-counterexample-have-a-nonsofic-core`.

`filtercheck.py` on 3x3, q = 2: of the 68 orbits that F1, F3 or F4 exclude, every F1-failing or F3-excluded
table carries exactly the 2 trivial `Dec` rules. 33 F4-excluded tables carry nontrivial `Dec` rules, as
expected, since F4 is a group-level filter.

**Second stage** (`stage2.py`), per survivor:
1. *Sofic exclusion.* `tietze2.decide` (binary census, md5 `977d57eb`): if `P(T)` is cyclic, free, or free
   abelian of rank two, it is sofic and no strict data have realized forward table `T`.
2. *Degenerate labels.* Labels equal after Tietze substitution and free reduction are equal in `P(T)`, so the
   table belongs to a smaller shape, which is excluded (sections 1, 3 and the binary census).
3. *Lower bound.* Reverse cells equal after substitution and free reduction are equal in `P(T)`. That
   partition `T_lb` is finer than `T_r^P`, so UNSAT at `(T, T_lb)` implies UNSAT at `(T, T_r^P)`.
4. Tables satisfiable at `T_lb` go to the exact stage: the binary census's `oracle.py` and `certify.py`,
   then encoding A at the realized pair.

Calibration on 3x3, q = 2: 92 survivors; 48 cyclic and 2 free abelian; 38 UNSAT at the lower bound, all 38
DRUP proofs VERIFIED; 4 escalated (orbit mass 10). This is consistent with the binary census.

RESULTS PENDING (MSI job 785182, `run_stage2.sbatch`).

## 6. Gap

PENDING.

## 7. Reproduction

| script | md5 |
|---|---|
| `satcensus.py` | `7d4aef11` |
| `satcensus2.py` | `934129a4` |
| `checkmodel.py` | `e4d37953` |
| `enum4.py` | `e673be70` |
| `filtercheck.py` | `e694aba4` |
| `stage2.py` | `9bf57da7` |
| `run_q3.sbatch` | `b7feeaea` |
| `run_stage2.sbatch` | `aa5477a0` |
| binary census `tietze.py`, `tietze2.py`, `oracle.py`, `certify.py`, `enum_tables.py` | `39f1a2ac`, `977d57eb`, `30c8f450`, `7c5cd981`, `bd32a62a` |

Python 3.12 venv with `python-sat` 1.9.dev15 and numpy 2.5.3.
