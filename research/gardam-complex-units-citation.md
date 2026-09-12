---
rg: 2
id: gardam-complex-units-citation
kind: route
title: Import Gardam's nontrivial units of the complex group ring of the Promislow group
target: unit-conjecture-fails-over-complex-numbers
requires: []
---

**Source.** G. Gardam, *Non-trivial units of complex group rings*,
arXiv:2312.05240 (v1 8 Dec 2023, v2 29 Oct 2024),
<https://arxiv.org/abs/2312.05240>. Accompanying code: zenodo record
14008425.

**Abstract (verbatim).** "The Kaplansky unit conjecture for group rings is
false in characteristic zero."

**Theorem A.** The torsion-free group

```text
P = <a, b | b^(-1) a^2 b = a^(-2), a^(-1) b^2 a = b^(-2)>
```

has "non-trivial units" in `C[P]`, with an explicit unit of support size 21.

**Coefficient ring (proof of Theorem A).** With `x = a^2`, `y = b^2`,
`z = (ab)^2` and `R = Z[s,t]/<s^4+1, t^4+1>`, the paper gives explicit
`alpha, beta in R[P]` with `alpha beta = 1`, both of support size 21. The
unit of the theorem is the specialization `s = t = zeta_8`. So the units lie
in `Z[zeta_8][P]`. Verbatim: "Since the unit has coefficients in Z[zeta_8],
it yields units in characteristic p for all primes p". The Corollary says the
21-element set supports nontrivial units over `F_(p^2)` for every prime `p`,
and over `F_p` when `p = 2` or `p = 1 mod 8`.

**What the paper leaves open (verbatim, Section 2).** "We have not succeeded
in finding a non-trivial unit in Z[P] but note that the coefficients in the
theorem are at least algebraic integers."

**Section 3 (search method).** Units `u` and `u^(-1)` supported on the two
fixed 21-element sets form a system of 121 bilinear equations in 42 unknowns.
Localizing to `u_1 = 1`, `u_2 != 0`, a Groebner basis modulo `p = 1000000007`
has coefficients `+-1` and exactly 16 solutions over `C`, parametrized by two
primitive eighth roots of unity. This holds "modulo the unlikely possibility
that p = 1000000007 is a bad prime". The paper also notes that lifting the
`F_2` solution 2-adically fails on these sets, because every
characteristic-zero solution needs an eighth root of unity and `Z_2` has no
square root of `-1`.

**Identification.** This presentation is exactly the Promislow group used in
`promislow-radius4-one-sided-and-integral-separation`.

**Trust surface.** Lane `unit-conjecture-integral` (2026-09-12) read the
arXiv v2 HTML in full on MSI, extracted the v2 PDF with ghostscript, and
downloaded the zenodo code. The Theorem A unit was recomputed exactly in
`R[P]` by `research/artifacts/gardam-support-pair-gsp.py`: `alpha beta =
beta alpha = 1`, both supports have size 21 and equal the sets of the zenodo
script `unit_problem.py`, and every coefficient is a signed monomial
`+-s^i t^j`. The earlier web extraction by the `zero-divisor-swarm` lane is
superseded.
