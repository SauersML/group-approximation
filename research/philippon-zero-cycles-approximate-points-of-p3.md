---
rg: 2
id: philippon-zero-cycles-approximate-points-of-p3
kind: claim
title: Philippon (JNT 81, 2000), Theoreme 1 with d = 0 - every point of P_n(C), n <= 3, is approximated by irreducible zero-dimensional cycles over Q with log Dist(x, Z) <= -(4c_n)^(-n) (h(Z) Delta + d(Z)(H + log(Delta + 1)))
distinct_from:
  philippon-zero-cycle-approximation-conjecture: that is the conjecture in every dimension n; this is the published theorem, which gives its distance inequality for n <= 3 only.
  algebraically-independent-points-approximable-by-zero-cycles: that is the Mahler-measure ratio statement the Atiyah base change needs for all s >= 3; this is the Diophantine theorem that implies its case s = 3.
---

**ESTABLISHED (literature import)** by
[[philippon-zero-cycles-approximate-points-of-p3-citation]], read from the
journal PDF.

**Statement (Theoreme 1 of JNT 81, specialised to d = 0).** Let
`n in {1, 2, 3}` and `c_n = 2^(n+4) n!`, so `c_1 = 32`, `c_2 = 128`,
`c_3 = 768`. For every `x in P_n(C)` and all integers `H >= 1` and
`Delta >= (4 c_n)^(n+1)` there is a cycle `Z` of dimension 0, irreducible over
`Q`, with

```text
d(Z) <= (c_n Delta)^n,
h(Z) <= n log(n+1) c_n^n (H + Delta) Delta^(n-1),
log Dist(x, Z) <= -(4 c_n)^(-n) (h(Z) Delta + d(Z) (H + log(Delta + 1))).
```

No hypothesis on `x`: it holds at every complex point.

**Notation (JNT 81, p. 235-236).**
- `d(Z)` is the degree and `h(Z) = m(g) >= 0` the height, where
  `g in Z[u]` is the eliminant (Chow) form of `Z` of content 1 and
  `m(g) = integral over S_(n+1)(1) of log|g| + deg(g) sum_(i=1..n) 1/(2i)`.
  The degree term is exactly the correction that makes `m` of a linear form
  the log of its Euclidean norm, and `m` is additive over products.
- `Dist(x, Z)` compares `m(d_x g)` with `m(g)`, where `d_x` substitutes
  `u_j = sum_k s_(j,k) x_k` with `s_(j,k) + s_(k,j) = 0`. The functions
  `d(.)`, `h(.)` and `log Dist(x, .)` are extended to cycles by linearity.
  For a point, `Dist(x, alpha) = ||x ^ alpha|| / (||x|| ||alpha||)`.
- **Zero-dimensional case.** Here `g = c prod_(alpha in Z) (u . alpha~)`,
  and `u . alpha~` becomes the linear form in `s` with coefficient vector
  `x ^ alpha~`. So, with `||x|| = 1`,
  `log Dist(x, Z) = sum_(alpha in Z) log Dist(x, alpha) + O_n(d(Z))`.
  The author's own restatement of the zero-dimensional case
  (hal-00480924, 2007, p. 2) writes `sum_(alpha in Z) log Dist(x, alpha)` and
  cites JNT 81 for the notation. Every use in the graph absorbs `O_n(d(Z))`
  into the `d(Z) H` term.

**Dimension four and up.** The author says (p. 235) that his lower bound for
the geometric Hilbert function, the tool that reaches codimension 3, "n'est
pas suffisante pour etendre nos resultats en codimension > 3". For `d = 0` this
is `n <= 3`. In hal-00480924 (pp. 2-3) he calls the zero-dimensional
conjecture open for `n > 3`, blocked only by an effective lower bound for the
arithmetic Hilbert function.

**Credit boundary.** For `s = 2`, the construction of
`research/artifacts/atiyah-two-variable-base-change-2026-09-13-part3.md`
(Minkowski on one bivariate and one univariate polynomial, then the Chow form
of `V(p_1, q)`) is an elementary, self-contained proof of a weak special case
of this theorem with `n = 2`. It gives only the ratio statement, with worse
constants and no degree or height budget. The new content of that artifact is
the operator side and its link to the Atiyah base change.
