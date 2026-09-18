# Two-cell core ratio search (2026-09-17)

Question: does a folded graph `Γ ⊂ X_H` (for `G = ⟨S | w⟩`, `w ∈ [F,F]`, not a proper power) carry two
distinct w-cycles (lifts of the 2-cell at two different vertices) with dependent classes
`[u_0] = a p`, `[u_1] = b p` in `H_1(Γ)` and `ab ≠ 0`, in degree-one form `ε_0 b - ε_1 a = ±1`,
e.g. `(a,b) = (1,2)`? Such a core is the ab ≠ 0 case of `two-cell-core-deletions-need-a-unit-fox-coefficient`.

Both circles read `w` in the same direction (`ε_0 = ε_1 = +1`). A configuration counts only when the
folded graph is connected and the two base points stay distinct. `ratio` returns `(content(v0), b)`.

## Runs

| script | parameters | configurations | hits with ab≠0, abs(a)≠abs(b) |
|---|---|---|---|
| `search.py` | MAXLEN 8, K ≤ 2 identifications, 2 gens | all | 0 |
| `search.py` | MAXLEN 8, K ≤ 3, 2 gens (16 words) | all | 0 |
| `search.py` | MAXLEN 10, K ≤ 2, 2 gens (92 words) | all | 0 |
| `search2.py` | MAXLEN 8, 2 gens, 3000 surface gluings per word | sampled | 0 |
| `rand3.py` | `2 4 14 20000 1` (length 4–14, 1–6 random identifications) | 20000 | 0 |

`rand3.py 2 4 14 20000 1`, full tally:

```
none 12882   indep 6419   (1,-1) 353   (0,0 zero) 118   (0,1 zero) 80   (1,0 zero) 74
(2,-2) 43   (3,-3) 23   (1,1) 6   (4,-4) 2
```

Example rows (word, identifications, rank, v0, v1):

```
(1,-1)   xYYXYXyxyy      [(11,5),(13,17),(12,17)]                3 [-1,1,0] [1,-1,0]
(1,1)    YYXyyyyxYY      [(18,9),(17,4),(7,3),(0,19)]            3 [-1,0,1] [-1,0,1]
(2,-2)   xyXXYYXXYxyxxy  [(14,23),(19,23),(3,13),(2,14)]         3 [2,-2,0] [-2,2,0]
zero 1,0 YxxyXX          [(5,10),(7,5),(6,10),(6,6),(7,9)]       3 [1,-1,0] [0,0,0]
```

## Reading

Every dependent pair found was of one of two kinds.

- `abs(a) = abs(b)`, i.e. `[u_1] = ±[u_0]`. Then `ε_0 b - ε_1 a ∈ {0, ±2a}`, which is never degree
  one. The augmentation of `c` is `0` or `±2a p`, which is not unimodular, so by (U2) such a pair is
  not admissible. The torus is of this kind.
- One class is zero (`ab = 0`). This is the Fox-singleton regime of (U4).

No `ab ≠ 0` degree-one configuration, such as `(1,2)`, appeared. This is a negative computation only.
Conjecture it suggests: a two-cell core of a degree-one admissible base always has `ab = 0`.
