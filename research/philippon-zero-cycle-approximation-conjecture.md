---
rg: 2
id: philippon-zero-cycle-approximation-conjecture
kind: claim
title: Philippon's conjecture - every point of P_n(C) is approximated by zero-dimensional cycles over Q with sum of log projective distances below minus (h(Z) D + deg(Z) H)/c_n
distinct_from:
  algebraically-independent-points-approximable-by-zero-cycles: that is the weaker ratio statement the Atiyah base change needs, phrased through Mahler measures of Chow forms; this is the literature conjecture with explicit degree and height budgets.
---

**OPEN (literature conjecture) for `n >= 4`. Its distance inequality is proved
for `n <= 3`** by Philippon, JNT 81 (2000), Theoreme 1 with `d = 0`, read from
the journal PDF: [[philippon-zero-cycles-approximate-points-of-p3]].

The statement is quoted from P. Philippon, *Approximations fonctionnelles des
courbes des espaces projectifs*, preprint hal-00480924 (2007), p. 2, and was read
from the PDF. Here `h` is the projective height on `P_n(Qbar)` and `Dist` the
projective distance on `P_n(C)`.

> **Conjecture.** There is a real `c_n >= 1` such that for every `x in P_n(C)`
> and all sufficiently large reals `H, D` there is a cycle `Z ⊂ P_n(Qbar)` of
> dimension 0, defined over `Q`, with `deg(Z) <= D^n`,
> `h(Z) <= (H + D) D^(n-1)` and
> `sum_(alpha in Z) log Dist(x, alpha) <= -c_n^(-1) (h(Z) D + deg(Z) H)`.

**Status, according to the author (same preprint, pp. 2-3).**
- **Small dimension.** He says he proved the conjectures of his JNT 64 (1997)
  paper (problems 7a, 10a) in
  *Approximations algebriques des points dans les espaces projectifs I*,
  J. Number Theory 81 (2000) 234-253, "en nous limitant a la dimension <= 3 ou
  a la codimension <= 3 selon les types d'enonces".
- **Dimension > 3.** He says the only obstacle to the arithmetic version is an
  effective lower bound for the arithmetic Hilbert function of a projective
  variety over `Q`, parallel to the Chardin-Philippon lower bound for geometric
  Hilbert functions.
- **Checked against JNT 81 on 2026-09-13.** The small-dimension result is
  Theoreme 1 (p. 236), stated for `max(0, n-3) <= d <= n`. So `d = 0` needs
  `n <= 3`.
  - For `d = 0` it gives `d(Z) <= (c_n Delta)^n`,
    `h(Z) <= n log(n+1) c_n^n (H + Delta) Delta^(n-1)` and
    `log Dist(x, Z) <= -(4c_n)^(-n) (h(Z) Delta + d(Z)(H + log(Delta+1)))`,
    with `c_n = 2^(n+4) n!`.
  - That is this conjecture's shape for `n <= 3`, with other constants.
  - p. 235: the Hilbert-function lower bound "n'est pas suffisante pour
    etendre nos resultats en codimension > 3".
- **What was not checked.** The status after 2010 was not searched.

## Attempts

* **Literature retrieval (bounded).** The HAL preprint was read.
  - **First attempt.** The JNT 81 article could not be retrieved: ScienceDirect
    serves a bot page, and the Elsevier API returns metadata only.
  - **Retrieved on 2026-09-13.** CORE output 82328610 was fetched through the
    Wayback snapshot (details in
    `philippon-zero-cycles-approximate-points-of-p3-citation`).
