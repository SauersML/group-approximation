# Integral reflection realizations of right-angled Coxeter groups in GL_3(Z)

Node: `sl3z-racg-witnesses-are-antiflag-configurations`. Lane:
`zaremsky-3-04-sl3z-coherent`. Every script runs single-threaded with numpy
only.

## Model

- A vertex is an integral anti-flag `(p, L, d)`: `p` and `L` primitive,
  `d = L·p` in `{1, 2}`. Its reflection is `s = I - (2/d) p L^T`
  (`antiflag.py`).
- Two vertices are adjacent iff they are mutually incident.
- A non-edge is "bad" iff it has finite order, which happens exactly when
  `a_uv a_vu` lies in `{1, 2, 3}`.

`kernel.py` is an exact kernel search. It enumerates elements of `W_Gamma`
faithfully through the contragredient Tits representation and hashes their
3x3 integer images; two words with the same image give a relator.

## Calibration (`driver.py`, `calibrate.out`)

- The `(inf, inf, inf)` Tits representation has no kernel up to length 12
  (12286 elements), as expected.
- Three reflections with a common centre give a kernel relator at length 3,
  also as expected.

## Searches

| script | rules | anti-flag box | best `4 chi` | outcome |
|---|---|---|---|---|
| `round2.py` (`round2_B1_B2.out`) | R0 + no product collisions | B=1 (117) | 5 (V=30, E=61) | kernel length 3 |
| `round2.py` | same | B=2 (1065) | 56 (V=153, E=358) | kernel length 3: `a`, `c` share centre `(0,0,1)`, and `b` has an axis through it |
| `round3.py` | + all non-edges loxodromic | B=1, 2 | 0 | none positive |
| `round4.py` | + no shared centre or axis at all (and, in the second run, no one-sided zero) | B=2 | 0 | none positive |
| `round5.py` | R0 + R1 + R2 + R3 + no product collisions | B=1, 2 | 0 | none positive |
| `orbits.py hyper` | R0–R3, unions of ≤2 orbits of the signed-permutation group (48) | B=2 (57 orbits), B=3 (233 orbits) | ≤ -8 | none positive |
| `orbits.py hex` | R0–R3, unions of ≤3 orbits of the hexagonal group (24) | B=2 (74 orbits) | only a single vertex scores positive | none with V ≥ 3 |

R0 means: no bad non-edge, triangle-free, `K_{2,3}`-free. Rules R1–R3 are
proved in the node.

## Exact search: the Robertson graph (`exact.py`, `exact_B1.out`, `exact_B2.out`)

The Robertson graph is the (4,5)-cage: 19 vertices, 4-regular, girth 5, and
`chi(W) = 1`. By (R6) a girth-5 graph admits no shared centre or axis, so the
rules R1-R5 give no constraint on it beyond distinctness. (It is not the
smallest girth-5 graph with `chi > 0`: deleting two adjacent vertices leaves
17 vertices, 31 edges and `chi = 1/4`.) `exact.py` is an exhaustive
backtracking search over anti-flags with entries in `[-B, B]`:

- vertex 0 is fixed up to signed permutations;
- forward checking with minimum-remaining-values ordering;
- constraints: (A2), (A3), and distinct centres and axes (R6).

| B | anti-flags | root orbits | nodes | deepest partial assignment | realizations |
|---|---|---|---|---|---|
| 1 | 117 | 10 | 2366 | 6 of 19 | 0 |
| 2 | 1065 | 57 | 3603369 | 8 of 19 | 0 |

So no reflection representation of the Robertson group in `GL_3(Z)` has all
of its anti-flags in the box `B <= 2`, even before any kernel test.

### The 17-vertex subgraph (`exact.py B rob17`, `exact_rob17_B1.out`, `exact_rob17_B2.out`)

`rob17` is the Robertson graph minus the adjacent vertices 0 and 1: 17
vertices, 31 edges, girth 5, minimum degree 3, `4 chi = 1`. It is an induced
subgraph, so this search is strictly stronger than the one above: any
Robertson realization restricts to a `rob17` realization.

| B | anti-flags | root orbits | nodes | deepest partial assignment | realizations |
|---|---|---|---|---|---|
| 1 | 117 | 10 | 2721 | 6 of 17 | 0 |
| 2 | 1065 | 57 | 2012645 | 9 of 17 | 0 |

So `W_rob17`, a two-dimensional incoherent right-angled Coxeter group, has no
reflection representation in `GL_3(Z)` satisfying (A2), (A3) and (R6) with all
anti-flags in the box `B <= 2`. The box is not invariant under `GL_3(Z)`, so
this rules out only small-height realizations.

## Reading

Every positive-Euler configuration the unconstrained search finds dies
through the shared-centre transvection mechanism. The proved rules R1–R3
remove exactly that mechanism, and then no positive configuration is found
in these ranges. The searches are heuristic: annealing, and orbit unions of
bounded size. This is not a proof of non-existence.
