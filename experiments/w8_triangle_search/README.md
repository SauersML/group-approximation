# Search for a W(8) triangle table

`GGT/KazhdanHypSharpExistenceAssembly.lean` and its residual form
`GGT/KazhdanHypSharpExistenceResiduals.lean` reduce the torsion-free hyperbolic
Kazhdan group behind `TheoremC.kotowskiOllivier` to two universal girth-eight
residuals and ONE finite object: a `GQEightTableFormat.W8Table 1755` with
`checkTable T.toTable = true`.  No such table existed anywhere in the repository
or in the campaign notes as of 2026-09-11.  This directory is the search for one.

## The object

A triangle table for the symplectic quadrangle W(8) (585 points, 585 lines, 9
points on a line, 9 lines on a point) is a bijection `lambda : points -> lines`
and 1755 rows `(x,y,z)` with `y in lambda(x)`, `z in lambda(y)`, `x in lambda(z)`,
closed under rotation, such that every arc `(x,y)` with `y in lambda(x)` is a
corner of exactly one row, and no row is `(x,x,x)`.  Then the presentation link
is the W(8) incidence graph through `lambda`, of girth 8 and normalized gap 5/9.
A polarity cannot serve as `lambda`: a generalized quadrangle has no triangles,
so its polarity graph has no nondegenerate directed three-cycles.  `q = 8` is
forced, since the Garland gap `1 - sqrt(2q)/(q+1)` exceeds `1/2` only from
`q = 7`, and `q = 7` fails integrality of the row count.

## Coordinates

`w8model.py` builds W(q) in the coordinates of
`GGT/KazhdanHypSymplecticQuadrangle.lean`: `GF(8) = GF(2)[t]/(t^3+t+1)`,
`B(x,y) = x0*y2 + x1*y3 - x2*y0 - x3*y1`, points the normalized nonzero vectors
of `GF(8)^4` in lexicographic order, lines the totally isotropic planes as sorted
tuples of point indices.  It also finds, by random symplectic transvections, an
element `sigma` of a prescribed order acting freely on points and lines.

## The encoding

`w8encode.py` writes the exact cover of sigma-invariant tables as CNF (the
variables and clauses are documented in its header).  sigma-invariance makes
`lambda` sigma-equivariant, so the search runs over orbit representatives.
`w8decode.py` re-verifies a model from scratch (lambda bijective, the row count,
the three incidences of every row, exact cover of every arc, no cube) and writes
`table.json`.

## Calibration on W(2) (15 points, 15 rows), 2026-09-11

* No symmetry (order 1): **SAT**; the decoded 15-row table passes every check.
  So the encoding admits tables where tables exist (the published GQ(2,2) triangle
  presentations are in `GGT/KazhdanHypGQTwoTable.lean`).
* Order 5 = q^2+1 (the Singer-type torus): **UNSAT**.  No W(2) table is invariant
  under it, so the analogous order-65 symmetry at q = 8 is not automatically
  available.
* Order 3: W(2) has no element of order 3 acting freely on both points and lines
  (such an element fixes a syntheme), so there is nothing to test.

## Which symmetries are available at q = 8

`w8model.py` accepts only an element acting freely on points AND lines, since
the encoding indexes lambda by orbit representatives and shifts.  Random products
of symplectic transvections (20000 tries per order, 2026-09-11) found free
elements of orders 65, 13 and 5, the subgroups of the Singer-type torus, and none
of orders 3, 9, 15, 39, 45, 117 or 195.  So the free-symmetry searches are the
three torus subgroups: order 65 (9 orbits), 13 (45 orbits), 5 (117 orbits).

## Jobs

* Job 407503 (2026-09-11 18:31–20:27, msismall node acn65, 16 cpus, 2 h): order
  65, 9 orbits.  CNF 4,122,465 variables and 12,388,455 clauses, 1,026,672
  triangle classes; encoding 16 s, 250 MB.  15 CaDiCaL 3.0.1 runs with seeds
  1–15, 110 min each.  **Result: UNKNOWN**, no run decided.  All cyclic subgroups
  of order 65 of Sp(4,8) are conjugate, so a decision either way would settle
  every table invariant under an element of order 65; none was reached.
* Pre-approved follow-up if that returns UNSAT or unknown: order 13 (45 orbits),
  `sbatch --export=ALL,ORDER=13 run_search.sbatch`.

Results are recorded here when the jobs finish.
