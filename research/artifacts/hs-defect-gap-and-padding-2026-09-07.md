# What the operator-norm certificate does not give: the Hilbert--Schmidt gap

2026-09-07.  Audit of a second external dossier, a negative one, on whether
the linear operator-norm inequality of
`research/artifacts/mf-radical-linear-certificate-2026-09-07.md` bears on
hyperlinearity.  Every displayed statement was re-derived here.  The dossier
is correct on all four points, and one of them was already recorded in the
graph in a stronger form.

Notation.  `Q=<S|R>` finitely presented, `|.|_2` normalized Hilbert--Schmidt,

```text
D_p(U) = max_(s in S) ||U_s - I||_p,
d_p(U) = max_(r in R) ||r(U) - I||_p.
```

## 1.  The statement that would decide the goal

A dimension-free `eta>0` with

```text
D_2(U) >= 1  ==>  d_2(U) >= eta                        (HSG)
```

makes `Q` non-hyperlinear.  A hyperlinear `Q` has `L(Q)` embedded in `R^omega`,
so the canonical trace kills every nonidentity group element, and the
microstates give unitary tuples with `d_2(U^((n))) -> 0` and
`||U_s^((n)) - I||_2 -> sqrt 2` for each `s != 1`.  Those tuples violate
`(HSG)` for large `n`.

The operator-norm inequality `D_infty(U) <= C d_infty(U)` does not give
`(HSG)`.

## 2.  The quantitative residue that it does give

For every unitary tuple with `D_2(U) >= 1`,

```text
1 <= D_2(U) <= D_infty(U) <= C d_infty(U) <= C sqrt d  d_2(U),
```

using `||a||_2 <= ||a||_op` and `||a||_op <= sqrt d ||a||_2` in normalized
Hilbert--Schmidt norm.  So

```text
d >= 1 / (C^2 d_2(U)^2).                               (DIM)
```

Hypothetical hyperlinear models of `Q` therefore have dimension growing at
least like the inverse square of their relator defect.  Their dimensions are
unconstrained, so this is not a contradiction.

## 3.  Why the compression proof does not transfer

Put `A_d = diag(-1,1,...,1) in U(d)`.  Then

```text
||A_d - I||_2 = 2/sqrt d -> 0,
||Ad(A_d) - id||_(B(M_d,||.||_2)) = 2,
```

the second by testing on `E_12`, which `Ad(A_d)` sends to `-E_12`.  Small
Hilbert--Schmidt relator error does not make the conjugation operators close
to the identity in the operator norm on `(M_d,||.||_2)`, which is what the
Kazhdan-projection step of the manuscript uses.  The finite-corona step
cannot be repeated in the Hilbert--Schmidt setting.

The graph already carries the decisive form of this firewall:
`simple-sofic-total-mf-radical` gives a countable simple sofic group `S` with
`Rad_MF(S)=S`, and sofic groups are hyperlinear, so no hypothesis-free
Hilbert--Schmidt version of the compression criterion can hold.  The dossier
makes the same point with the manuscript's `W`, which is sofic.

## 4.  Local rigidity near the trivial tuple is the whole problem

Suppose there were dimension-free `a,C>0` with

```text
D_2(U) < a  ==>  D_2(U) <= C d_2(U).
```

Pad by identities: `U~_s = U_s (+) I_(N-d) in U(N)`.  A word evaluates to
`r(U) (+) I_(N-d)`, and the normalized Hilbert--Schmidt norm scales exactly,

```text
D_2(U~) = sqrt(d/N) D_2(U),   d_2(U~) = sqrt(d/N) d_2(U).
```

Choose `N` with `sqrt(d/N) D_2(U) < a`, apply the local estimate to `U~`, and
cancel `sqrt(d/N)`.  The result is `D_2(U) <= C d_2(U)` for every tuple in
every dimension, which contains `(HSG)` with `eta = 1/C`.

So a dimension-free linear rigidity theorem in any neighbourhood of the
trivial tuple already solves the global problem, and property (T) is not a
substitute for it.  Dogon--Vigdorovich, arXiv:2506.20843v2, Theorem 4.1,
produce non-hyperlinear groups only under an added Hilbert--Schmidt
stability hypothesis on the lattice, which is the same additional input in
another form; the graph records that import as
`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`.

## 5.  Position in the graph

The qualitative form of `(DIM)` is already
`full-mf-radical-hyperlinear-models-force-relator-outliers`: hyperlinear
models of `Q` must carry a fixed operator-norm relator failure on a spectral
corner of vanishing trace.  What is new is the numerical dimension floor,
which needs the linear inequality, and the padding equivalence, which is
independent of it.

The verdict recorded on the goal `non-hyperlinear-group` is unchanged.  The
manuscript's operator-norm results do not prove non-hyperlinearity of `H` or
`Q`, and no node asserts that they do.
