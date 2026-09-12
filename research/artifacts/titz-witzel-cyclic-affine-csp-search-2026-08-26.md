# Titz--Witzel cyclic-affine CSP search, 2026-08-26

This artifact separates one exact symbolic result from exploratory finite
search.  The theorem in
`titz-witzel-cyclic-affine-ansatz-has-linear-defect` is the
word calculation reproduced by the verifier below.  The later search data
is evidence about attempted ansatzes only and is not used as a proof.

## Exact verifier

The following dependency-free Python code uses permutations as image lists
and the convention that a word acts from right to left.

```python
def compose(p, q):
    return [p[q[i]] for i in range(len(p))]

def inverse(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return q

def evaluate(word, variables):
    inverses = {name: inverse(p) for name, p in variables.items()}
    result = list(range(len(next(iter(variables.values())))))
    for letter in word:
        table = variables if letter.islower() else inverses
        result = compose(result, table[letter.lower()])
    return result

A, B, C = "xYY", "zYz", "yyx"
D, E = "zYzxY", "Yzz"
F, S, H = "XzzYx", "ZXyZZ", "zzY"
relators = [w + w for w in [A, B, C, E, F, S, H]] + [
    A + C + D + B,
    "xz" + C + S,
    A + E + D + F,
    D + F + E + H,
    D + S + F + E,
]

for n in [5, 7, 9, 11, 17, 31]:
    h, a = (n + 1) // 2, 0
    variables = {
        "x": [(-i + a) % n for i in range(n)],
        "y": [(i + 1) % n for i in range(n)],
        "z": [(i + h) % n for i in range(n)],
    }
    defects = []
    for word in relators:
        p = evaluate(word, variables)
        defects.append(sum(p[i] != i for i in range(n)))
    y8 = evaluate("yyyyyyyy", variables)
    marked = sum(y8[i] != i for i in range(n))
    print(n, defects, marked)
```

It returns

```text
5  [0,0,0,0,0,0,0, 4,4,5,4,5]       5
7  [0,0,0,0,0,0,0, 6,6,7,6,7]       7
9  [0,0,0,0,0,0,0, 8,8,9,8,9]       9
11 [0,0,0,0,0,0,0,10,10,11,10,11]  11
17 [0,0,0,0,0,0,0,16,16,17,16,17]  17
31 [0,0,0,0,0,0,0,30,30,31,30,31]  31
```

## Exact-square-manifold search

The useful parametrization behind a second search was:

```text
A=x y^(-2),                         r=z^2,
E=y^(-1)r.
```

The identities

```text
B=zEz^(-1),       H=yEy^(-1),       F=x^(-1)Hx
```

show that the four squares `B^2,E^2,F^2,H^2` are simultaneously exact once
`E` is an involution.  Also, after writing `x=Ay^2`, the pair `A^2=C^2=1`
is equivalent to

```text
A^2=1,                 A y^4 A=y^(-4).
```

For `y` a single odd cycle, reflection choices for `A` satisfy the latter
identity.  The search therefore enumerated or sampled involutions `E`, kept
only permutations `r=yE` admitting a square root `z`, constructed such roots,
and tested `S^2` and the five coupling equations exactly.  Deterministic
representative-root enumeration for `n=7,9,11` and randomized root sampling
for `n=17,31` found only coupling-error totals proportional to `n`; no
sublinear pattern appeared.  Unconstrained swap annealing likewise plateaued
at linear normalized error.

These finite observations exclude nothing beyond the proved affine family:
the search did not enumerate every square root at the larger sizes, and a
sofic approximation may use a completely different cycle structure for `y`.

## Direct search in the seven-relator variables

A second annealer worked directly with `(c,e,r)` from `(TW8)`.  Both `c` and
`e` were maintained as fixed-point-free involutions.  A matching move chose
two matching edges and replaced them by one of the cross-pairings; an `r`
move swapped two images, so all three variables remained permutations and
the two square equations stayed exact.  The score was

```text
sum of the five numbers of moved points
  +20 max(0,n/2-number of points moved by Y^8).
```

Starting from two random perfect matchings and a random permutation, one
million Metropolis steps used temperature
`3(1-step/1000000)+0.02`.  The recorded seeds and best states were:

| `n` | seed | five coupling defects | `supp(Y^8)` | total defect / `n` |
|---:|---:|:---|---:|---:|
| 12 | 21 | `3,0,3,0,6` | 6 | 1.000 |
| 20 | 22 | `6,0,10,6,4` | 10 | 1.300 |
| 28 | 23 | `12,6,12,13,15` | 16 | 2.071 |
| 40 | 24 | `19,4,18,18,19` | 20 | 1.950 |

The low-dimensional states sometimes solve two coupling words exactly, but
the total defect remains linear in the domain size and the ratio does not
suggest a scalable family.  Annealing is heuristic: this table is neither a
lower bound nor evidence of infeasibility outside this search landscape.

## Reproducible occurrence counts for the support bounds

The constants in `titz-witzel-trivial-second-matching-collapses-mark` and
`titz-witzel-both-matchings-need-macroscopic-support` come from ordinary
fixed-word telescoping.  Counting occurrences after recursively expanding
`(TW8)` gives

| word | occurrences of `e^+-1` | occurrences of `c^+-1` |
|:---|---:|---:|
| `Y` | 1 | 0 |
| `X` | 2 | 1 |
| `A'` | 4 | 1 |
| `D'` | 4 | 1 |
| `F'` | 5 | 2 |
| `S'` | 3 | 1 |
| `H'` | 1 | 0 |
| coupling word 2, `XrcS'` | 5 | 3 |
| coupling word 3, `A'eD'F'` | 14 | 4 |
| coupling word 4, `D'F'eH'` | 11 | 3 |
| mark `Y^8` | 8 | 0 |

Only the following logical dependencies are used in the estimates: the
`e`-counts `14,11,8` give

```text
8*14+16*11+8=296,
```

while the `c`-counts `3,4,3`, followed by the factor `296`, give

```text
8*4+16*3+296*3=968.
```
