---
rg: 2
id: steinberg-five-seven-full-minor-proof
kind: route
title: Replay nonsingular full-column flag minors over F5 and F7
target: steinberg-flag-fox-map-is-injective-at-five-and-seven
requires:
  - steinberg-fox-kernel-is-flag-incidence
artifacts:
  - experiments/steinberg_fox_flag_screen.py
  - research/artifacts/steinberg-fox-primes-3-5-7-2026-09-04.jsonl
---

Use residues `0,...,p-1`.  Normalize each projective vector by making its
first nonzero coordinate one, then order the normalized triples
lexicographically.  Order flags `([v],[w])` lexicographically as pairs of
these triples subject to `w^T v=0`.

The boundary has points first and planes second, in the same projective
order, and its column for `(v,w)` has `-1` in the point row and `+1` in the
plane row.  Stack rows in the order `partial, X, Y`; the rows of each Fox
operator use the flag order.  All indices in the JSONL certificate are
zero-based indices into this stack, and each minor uses every column in
its original flag order.

Here are the complete coefficient conventions, with elementary matrices
acting on column vectors:

```text
h=diag(2,1,1/2),              d12=diag(2,1/2,1),
q=x21(-1/2),                  s=x32(-1/2),
A=x12(2),                    B=d12*x23(2),
u=q*x13(1)*q^(-1),           r=x23(-1),
X=A-Aq+B-Bs-1,
Y=1-q-u+uq-h^(-1)r+h^(-1).
```

The permutation matrix for `g` sends the column indexed by `(v,w)` to the
row indexed by `(normalize(gv),normalize(g^(-T)w))`.  Thus its entries and
all entries of the stacked matrix are specified by finite arithmetic,
independently of either elimination algorithm.

The exact certificate replay gives:

| p | Flags | Rank of boundary | Rank of (boundary,X) | Rank of D_p | Full-minor determinant |
|---|---:|---:|---:|---:|---:|
| 3 | 52 | 25 | 49 | 52 | 2 mod 3 |
| 5 | 186 | 61 | 181 | 186 | 4 mod 5 |
| 7 | 456 | 113 | 448 | 456 | 3 mod 7 |

The `full_minor_rows` arrays in the artifact identify the three minors
exactly.  In each case the determinant is nonzero, so `D_p` has zero
kernel.  The required flag-incidence identification then gives the
zero-common-kernel result on `St_p`.  The characteristic-three row is a
cross-check against the pre-existing proof; the new cases are five and
seven.

The replay program first selects a minor by integer, prime-field
elimination on the transpose.  It then independently computes the selected
square minor's determinant by sparse scalar row elimination and checks
agreement.  Neither algorithm uses floating-point rank or a numerical
tolerance.  The checks also recover
`dim ker(partial)=p^3` and verify that every coefficient action permutes
the complete flag set.

The checked run used one remote process on MSI `acn116`; each case took
less than two seconds.  A preliminary characteristic-eleven run of the
older scalar implementation reached its 25-second timeout and supplies
no conclusion.  No characteristic-eleven claim is made.

Reproduce with Python and NumPy on a compute node:

```text
python experiments/steinberg_fox_flag_screen.py 3 5 7
```

Injectivity at finitely many primes cannot be extrapolated to all primes.
Even the uniform Steinberg theorem would address only one coefficient
sector, leaving the arbitrary-microstate stability obstruction open.
