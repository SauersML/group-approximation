# Two-cell cores with ab != 0: fiber-product construction and admissibility certificates

Lane w9-048, 2026-09-18. These scripts support
`degree-one-two-cell-cores-with-ab-nonzero-exist` and
`two-cell-ab-nonzero-admissible-needs-g-in-conj-closure`.

The conventions follow `two-cell-core-deletions-need-a-unit-fox-coefficient`. Folded graphs use the
letters x, y (0 = x, 1 = y). The abelianization `G^ab = Z^2` has `x -> t` and `y -> s`, which is valid
because every `w` produced here lies in `[F,F]`.

## Scripts

| file | what it does |
|---|---|
| `fp.py` | Enumerates the connected folded core graphs of rank at least 2 on n vertices. For each off-diagonal component `Delta` of `Gamma x_S Gamma`, it tests whether some `h in H_1(Delta)` has `p2_* h = lam p1_* h != 0`, by exact rank over Q, for `lam in {2, 3/2}`. |
| `words.py` | Runs a DFS for cyclically reduced words that are not proper powers and read closed loops at `v0 = 0` and `v1 = 1` of one fixed graph with `z1 = lam z0`. |
| `abel.py` | Computes the cylinder row `c` of the explicit example over `Q[s^+-,t^+-]` (one choice of basis) and runs a Groebner test. |
| `census.py` | Helpers: the transition table, reading words, Fox row `crow` (`c_x = g d_x u0 - d_x u1` with a spanning tree from `v0`), and Groebner `unit`. |
| `finchar.py` | For every graph on n vertices, every off-diagonal fiber-product component and every `lam`, it builds one word from the first nullspace vector `h`, adds a commutator, and freely and cyclically reduces. It then (i) searches for an exact certificate of non-admissibility, a character `chi: G -> F_q^*` (q prime, at most 61) with `c^chi = 0`; and (ii) tests the abelian shadow of Theorem B', that `[g]` lies in the image of `H_1(H) -> Z^2`. |
| `gcdfac.py` | Same configurations. It compares the gcd of the entries of `c` in `Q[s,t]` with the Alexander polynomial `d w / d y` of `w`. |
| `example_check.py` | Exact checks of the explicit example: closed loops, classes `z1 = 2 z0`, factored `c`, and `c` at `(s,t) = (-1,2)`. |
| `cover3.py` | Shows that the index-3 cover `X_K` (with `x = (1 2)`, `y = (0 1)`) is `C` plus one edge `f` and one 2-cell, and prints that 2-cell. |
| `lowindex.g` | GAP. Finds the subgroups of index at most 8 that contain `H` and separate the vertices 0, 1, 2. |

Every run uses `nice -n 10 timeout 1200 python3 <script> <n>`, single-threaded.

## Runs

1. `fp.py 2`: 15 graphs, 0 hits. No ratio-`lam` pair exists on a 2-vertex graph for `lam in {2, 3/2}`.
   `fp.py 3`: 404 graphs, and 66 of them carry pairs for both `lam = 2` and `lam = 3/2`.
2. `words.py 16` on the graph `[(0,0,x),(1,2,x),(0,1,y),(1,0,y),(2,2,y)]` finds
   `w = x y^4 x^-1 y^-1 x y^2 x^-1 y^-5` with `lam = 2`, `z0 = [0,0,-1,-1,2]` and
   `z1 = [0,0,-2,-2,4]`.
3. `example_check.py`:
   - `c = ( s(s-1)(s+1)f, -s f (st-s+1), st(s+1) f )`, where `f = s^3 - s^2 - 1`.
   - At `(s,t) = (-1,2)` we get `c = 0`. So the rational character `x -> 2`, `y -> -1` kills `c`.
   - `c` also vanishes on the whole curve `f(s) = 0`.
   - The sign character `(s,t) = (-1,-1)` gives `c = (0,-9,0)`.
   - The Alexander polynomial of `w` is `(s+1)(t-1)(s^3+s^2+1)`, and `f(s) = -(s^3+s^2+1)|_{s -> -s}`.
4. `lowindex.g`: 109 subgroups of index at most 8 contain `H`, and 108 of them separate the three
   vertices. This includes one of index 3, which is the cover of `cover3.py`.
5. `cover3.py`: `X_K^1` minus `Gamma` is the single edge `f = (2 -> 1, x)`. The lifts of `w` at
   vertices 0 and 1 avoid `f`. The lift at 2 is `f x | y^4 | f X | Y | f x | y^2 | f X | Y^5`.
6. `finchar.py 3` (output in `finchar3.out`):
   `{('Bprime-ok','nonadm-char','2'): 66, ('Bprime-ok','nonadm-char','3/2'): 66}`.
   - All 132 ratio configurations built this way are non-admissible, each with an exact `F_3`
     character certificate: `(s,t) = (2,1)` for `lam = 2` and `(2,2)` for `lam = 3/2`.
   - All 132 pass the abelian shadow of Theorem B', so that shadow alone does not decide them.
7. `gcdfac.py 3`:
   - In 96 of the 132 configurations the entries of `c` share a nontrivial factor in `Q[s]`.
   - In every case printed, that factor is the non-`(s+1)` part of the Alexander polynomial of `w`
     with `s -> -s`.
   - The other 36 have a trivial gcd but are still killed by an `F_3` character.

## What this rules out, and what it does not

- It rules out any proof of "`ab = 0` for every degree-one two-cell core" that uses only the folded
  graph, the two `w`-loops and `H_1`. Such cores with `(a,b) = (1,2)` exist (run 2, plus the proof
  in `degree-one-two-cell-cores-with-ab-nonzero-exist-proof`).
- It does **not** give an admissible `ab != 0` core. Every configuration found fails admissibility,
  through a character `chi` with `c^chi = 0`.
- The census builds one word per (graph, component, `lam`). It covers `eps = +1` only, `lam in
  {2, 3/2}`, and graphs with at most 3 vertices. It is evidence, not a proof, that the character
  test always kills `ab != 0`.
