# Gap tables inside Baumslag-Solitar groups

Supports `research/baumslag-solitar-gap-table-at-five-by-five.md`.

A forward table `T` (a rook-independent partition of `S x M`, with `1` in both memories) is a **gap table** when
some pair of reverse cells `x_m x_s`, `x_m' x_s'` is distinct in the table group `P(T)` but merged in every finite
quotient of `P(T)` (definition from `strict-pairs-need-a-memory-with-five-elements`). The finite-quotient census
of that claim can decide a table only if it is not a gap table. It found no gap tables up to shape `4x4`.

This experiment looks for gap tables directly, inside `G = BS(2,3) = <a, t | t a^2 t^-1 = a^3>`. The largest
residually finite quotient of `G` is `H = Z[1/6] x| Z`, with `t` acting as multiplication by `3/2`. So a reverse
pair is merged in every finite quotient of `G` exactly when the two products agree in `H`. When the table group
is `G` itself through the labels, a pair distinct in `G` and equal in `H` gives a gap table.

## Result

A gap table at shape `5x5`:

```
S = {1, a, t, a^3, t^-1 a t a^-1}        M = {1, a, a^2, t, t^-1 a t}
```

- Forward coincidences in `G` (all of them): `a*1 = 1*a`, `a*a = 1*a^2`, `t*1 = 1*t`,
  `(t^-1 a t a^-1)*a = 1*(t^-1 a t)`, `a*a^2 = a^3*1`, `a*t = t*(t^-1 a t)`, `t*a^2 = a^3*t`.
- Tietze elimination leaves `<x_a, x_t | x_t x_a^2 x_t^-1 x_a^-3>`, so `P(T) = BS(2,3)` through the labels.
  GAP's `SimplifiedFpGroup` gives the same presentation.
- Gap pair: `a * (t^-1 a t a^-1)` versus `(t^-1 a t) * 1`. These are distinct in `G` (Britton) and equal in `H`.
- Calibration against the census pipeline: `gapcensus.py reps 5 5` (Knuth-Bendix, Sims1 up to degree 7), and then
  `pass3.py` (Tietze, Sims1 up to degree 9), on this table report `CANDIDATE` with exactly this one unseparated
  pair (`[[1, 4], [4, 0]]` in their `(m, s)` indexing).

Two `5x6` gap tables (same base, `S` gains `t a^-1 t^-1`, `M` gains `t a^-1` or `t a^2` together with
`t a^-1 t^-1`) are in `gap_tables_5x6.jsonl`.

## Search counts

| run | pairs tested | with a gap pair in `H` | certified gap tables |
|---|---|---|---|
| `bsgapsearch.py 2 3 2 4 4` (all subsets of the radius-2 ball, 17 elements) | 313,600 | 1,560 | 0 |
| `bsgapsearch.py 2 3 2 4 5` | 1,019,200 | 10,088 | 0 |
| `bsgapsearch.py 2 3 2 5 4` | 1,019,200 | 10,088 | 0 |
| `bsgapsearch.py 2 3 2 5 5` | 3,312,400 | 64,882 | 0 |
| `extend.py 2 3 4 1,a,t,aaa 1,a,aa,t 4 5` (one new element from the radius-4 ball, 147 elements) | 143 | | 0 |
| `extend.py 2 3 4 1,a,t,aaa 1,a,aa,t 5 4` | 143 | | 0 |
| `extend.py 2 3 3 1,a,t,aaa 1,a,aa,t 5 5` | 2,401 | | 0 |
| `extend.py 2 3 4 1,a,t,aaa 1,a,aa,t 5 5` | 20,449 | | 1 |
| `extend.py 2 3 3 1,a,t,aaa 1,a,aa,t 5 6` | 57,624 | | 2 |

The `4x4` rows agree with the census (no gap tables at `4x4`). The certificate is sufficient, not necessary.
The zero rows therefore do not exclude gap tables at `4x5`. Indeed a `4x5` gap table exists: its memory `S`
contains `t^-1 a t`, outside the radius-2 ball (see the section on minimal gap shapes below).

## Files

- `bsgroup.py`: the word problem of `BS(p,q)` (Britton reduction, right normal form) and the map to `H`. It has a
  self-test: `python3 bsgroup.py`.
- `gaptable.py`: the forward table, Tietze elimination and the certificate.
- `bsgapsearch.py`: exhaustive search over a ball.
- `extend.py`: extends a base pair by ball elements.
- `verify_gap55.g`: an independent GAP check of the `5x5` table. It checks the presentation, the label
  homomorphism, and that the pair is unseparated by all 10 transitive representations of degree at most 8.
- `gap_tables_5x5.jsonl` and `gap_tables_5x6.jsonl`: the certified records.

## Reproduction

```
python3 bsgroup.py
nice -n 10 timeout 1200 python3 bsgapsearch.py 2 3 2 5 5 out55.jsonl
nice -n 10 timeout 1200 python3 extend.py 2 3 4 1,a,t,aaa 1,a,aa,t 5 5 gap_tables_5x5.jsonl
nice -n 10 timeout 1200 python3 extend.py 2 3 3 1,a,t,aaa 1,a,aa,t 5 6 gap_tables_5x6.jsonl
gap -q verify_gap55.g < /dev/null
```

# Minimal gap shapes: three by six and four by five

Supports `research/gap-tables-first-appear-at-three-by-six-and-four-by-five.md`.

## Gap tables at 3x6 and 4x5

Both tables have `P(T) = BS(2,3)` through the labels, with `u = t^-1 a t` and `H = Z[1/6] x| Z`.

- `3x6`: `S = {1, t, ta}`, `M = {1, a, a^-1, a^-2, a^-1 t^-1 a, a^-2 t^-1 a}`. The gap pair is
  `(a^-1 t^-1 a) * t` versus `(a^-2 t^-1 a) * (ta)`. The first record of `gap_tables_3x6.jsonl` is this table.
  The other four records are the hits of `schreiersearch.py` at `3x6`.
- `4x5`: `S = {1, a, t, u}`, `M = {1, a, t, u, u^2}`. The gap pair is `a * u` versus `u * a`. The first record of
  `gap_tables_4x5.jsonl` is this table. The other five records come from `schreiersearch.py` with `S` fixed.
- `gap_tables_3x12.jsonl`: an earlier hand-built `3x12` table.

`verify_gap36.g` is an independent GAP check of both tables. GAP 4 printed:

```
transitive representations of BS(2,3) of degree <= 8: 10
3x6: P(T) simplified: generators [ xt, ya ], relators [ ya^-3*xt*ya^2*xt^-1 ]
3x6: label map P(T) -> BS(2,3) is a homomorphism: true
3x6: gap pair distinct in BS(2,3) (a and t^-1 a t do not commute): true
3x6: transitive representations of degree <= 8 separating the gap pair: 0
4x5: P(T) simplified: generators [ xt, xu ], relators [ xt*xu^2*xt^-1*xu^-3 ]
4x5: label map P(T) -> BS(2,3) is a homomorphism: true
4x5: transitive representations of degree <= 8 separating the gap pair a*u, u*a: 0
```

For the `4x5` table the simplified letters are `x_t` and `x_u`, and `x_u -> a`, `x_t -> t` is the isomorphism onto
`BS(2,3)`. Composed with the label map, it is conjugation by `t`, which is inner.

## Directed search (`schreiersearch.py`)

`S` ranges over the 3-subsets of the radius-2 ball containing `1` (120 memories). `M` ranges over the connected sets
of the coincidence graph of `S` that contain `1`.

| shape | `M` tested | enough coincidences | with a gap pair in `H` | certified | `S` with a hit | seconds |
|---|---|---|---|---|---|---|
| `3x4` | 29,104 | 496 | 0 | 0 | 0 | 8.6 |
| `3x5` | 210,060 | 1,700 | 0 | 0 | 0 | 64.6 |
| `3x6` | 1,584,576 | 6,144 | 12 | 4 | 3 | 407.0 |

The zero rows agree with the census below. The certificate is sufficient, not necessary, so the census and not the
search proves that there is no gap table at `3x5`.

## Orderly enumeration with pruning (`enumtables6.c`)

Mode `prune` runs the difference closure after each completed row.

| shape | mode | raw | orbits | survivors | collision | NOTCLOSED | pruned subtrees |
|---|---|---|---|---|---|---|---|
| `3x3` | full = prune | | | 74 | | | |
| `3x4`, `4x3` | full = prune | | | 909 | | | |
| `4x4` | prune | 9,295,416 | 101,474 | 21,252 | | | |
| `3x5` | prune | 2,044,580 | 41,716 | 7,801 | 23,525 | 10,390 | 140 |
| `5x3` | prune | 1,166,568 | 18,931 | 7,801 | 5,587 | 5,543 | 13,908 |
| `3x6` | prune | 201,106,530 | 809,199 | 68,844 | 635,604 | 104,751 | 1,620 |

The `3x6` row (233 s of CPU) only sizes the next census, which has not been run. Pass 1 would need about 35 chunks.

The `3x4`, `4x3` and `4x4` survivor lists are byte-identical in `full` and `prune` mode. The `4x4` list is
byte-identical to `reps_4x4.txt.gz` of `experiments/gottschalk-residual-gap-census-2026-09-17`. The `3x5` and `5x3`
counts agree, as inversion of labels predicts.

## Census at 3x5 and 5x3

Every survivor ends as RESOLVED or NOTCLOSED. No CANDIDATE remains.

| shape | survivors | pass 1 (`gapcensus.py`, Sims1 degree <= 5) | pass 2 (`pass2.py`) | pass 3 (`pass3.py`) | final | `verify.py` |
|---|---|---|---|---|---|---|
| `3x5` | 7,801 | RESOLVED 6,609, NOTCLOSED 1,151, CANDIDATE 41 | all 41 RESOLVED | none left | RESOLVED 6,650, NOTCLOSED 1,151 | verified 6650 failed 0 |
| `5x3` | 7,801 | RESOLVED 6,609, NOTCLOSED 1,151, CANDIDATE 41 | 40 RESOLVED, 1 CANDIDATE | 1 RESOLVED | RESOLVED 6,650, NOTCLOSED 1,151 | verified 6650 failed 0 |

Pass 1 per chunk of 2,000:

- `3x5`: RESOLVED 1622, 1634, 1728 and 1625; NOTCLOSED 369, 353, 265 and 164; CANDIDATE 9, 13, 7 and 12. The chunks
  took 112 s, 165 s, 198 s and 185 s.
- `5x3`: RESOLVED 1670, 1587, 1734 and 1618; NOTCLOSED 319, 401, 259 and 172; CANDIDATE 11, 12, 7 and 11. The chunks
  took 113 s, 158 s, 197 s and 177 s.

Each final record's `table` equals line `id` of the survivor list, and the ids are exactly `0..7800`. `verify.py`
also runs unchanged on the `.gz` files. The equal final counts at `3x5` and `5x3` agree with inversion `g -> g^-1`,
which exchanges the two shapes and preserves the table group.

## Reproduction (additions)

Run from this directory. `C` is `../gottschalk-residual-gap-census-2026-09-17`.

```
gcc -O2 -o enumtables6 enumtables6.c
./enumtables6 3 5 prune > reps_3x5.txt ; ./enumtables6 5 3 prune > reps_5x3.txt
for k in 0 1 2 3; do a=$((2000*k)); b=$((2000*(k+1)));
  nice -n 10 timeout 1200 python3 $C/gapcensus.py reps 3 5 reps_3x5.txt 5 200 r35_$k.jsonl $a $b; done
for k in 0 1 2 3; do
  nice -n 10 timeout 1200 python3 $C/pass2.py 3 5 r35_$k.jsonl p2_35_$k.jsonl 7 2000 60
  nice -n 10 timeout 1200 python3 $C/pass3.py 3 5 p2_35_$k.jsonl p3_35_$k.jsonl 10 300; done
python3 $C/merge.py census_3x5.jsonl r35_*.jsonl -- p2_35_*.jsonl -- p3_35_*.jsonl
python3 $C/verify.py 3 5 census_3x5.jsonl
# the same four steps with 5 3, r53_*, p2_53_*, p3_53_* give census_5x3.jsonl
nice -n 10 timeout 1200 python3 schreiersearch.py 2 3 2 3 6 s3x6.jsonl
nice -n 10 timeout 1200 python3 schreiersearch.py 2 3 2 4 5 cal45.jsonl 5 1,a,t,Tat
gap -q verify_gap36.g < /dev/null
```

## Files (additions)

- `enumtables6.c`: the orderly enumerator, up to six labels per side, with in-search pruning.
- `census_3x5.jsonl.gz` and `census_5x3.jsonl.gz`: the final record of every survivor.
- `schreiersearch.py`: the directed search through the coincidence graph.
- `gaptable.py`: `certify_iso` and `certify2`, used by `schreiersearch.py`.
- `verify_gap36.g`: the GAP check above.
- `gap_tables_3x6.jsonl`, `gap_tables_4x5.jsonl` and `gap_tables_3x12.jsonl`: the records.
