---
rg: 2
id: promislow-classical-residues-shadow-computation
kind: route
title: Exact definite shadows of Gardam's unit, the radius-four census units and Murray's units are not monomials
target: promislow-classical-nontrivial-units-have-no-integral-lifts
requires:
  - promislow-integral-units-have-monomial-definite-line-shadows
  - promislow-radius4-one-sided-and-integral-separation
  - unit-conjecture-fails-over-complex-numbers
  - murray-z-only-ansatz-has-no-char0-units
---

**Shadow formulas.** Write `w = p + q a + r b + s ab` with
`p, q, r, s in F_d[x^(+-1), y^(+-1), z^(+-1)]`, coefficients on the left. By the
table of `promislow-integral-units-have-monomial-definite-line-shadows`, with
`w = l_0 + l_1 u` in `D(F_d)`:

- **C:** `l_0 = p(-1,-1,t^2) + t s(-1,-1,t^2)`,
  `l_1 = q(-1,-1,t^2) - t^-1 r(-1,-1,t^2)`;
- **A:** `l_0 = p(t^2,-1,-1) + t q(t^2,-1,-1)`,
  `l_1 = r(t^2,-1,-1) + t s(t^2,-1,-1)`;
- **B:** `l_0 = p(-1,t^2,-1) + t r(-1,t^2,-1)`,
  `l_1 = q(-1,t^2,-1) + t^-1 s(-1,t^2,-1)`.

A group element `x^i y^j z^k c` is read off Gardam's affine model
`a: v -> diag(1,-1,-1) v + (1,1,0)`, `b: v -> diag(-1,1,-1) v + (0,1,1)`, in
which `x, y, z` are the translations by `(2,0,0), (0,2,0), (0,0,-2)`.

**Case 1: Gardam's unit.** `research/artifacts/promislow-definite-shadows-residues.py`
imports `research/artifacts/gardam-support-pair-gsp.py`, which rebuilds Gardam's
unit `alpha` and inverse `beta` in `R[P]` and checks `alpha beta = beta alpha = 1`
exactly. Every coefficient is `+-s^i t^j`, so modulo 2 the residue of `alpha` is
the sum of its 21 support elements. Gate: the shadows of the residues of `alpha`
and `beta` multiply to `1` on each line. Result: shadow C is `1`; shadows A and B
are `t^-2 + 1 + t^2 + (t^-2 + t^2) u`, of norm `1`.

**Case 2: the census units.**
`research/artifacts/promislow-definite-shadows-census.py` reads the 52 census
supports from `census52.json` and the seven orbit representatives with their
inverse supports from `census_pairs.json`. These are the files used on MSI by
`research/artifacts/promislow-radius4-census.py` (mode `orbits`) and by the
2026-09-12 support-pair artifact; md5s are in the log. Gates:

- the file lists 52 supports of size 21;
- for each representative pair `(S, T)`, the shadows of `sum S` and `sum T`
  multiply to `1` in both orders on every line and have norm `1`;
- every one of the 52 residues has norm `1` on every line.

Result: all 52 have monomial shadow C and non-monomial shadows A and B.

**Case 3: Murray's units.** The same script as Case 1 builds Murray's ansatz
`p = (1+x)(1+y) f_1`, `q = (1+x)(x^-1+y^-1) f_2 + (1+y^-1) f_3`,
`r = (1+y^-1)(x+y) f_4 + (1+x) f_5`, `s = (x+4+x^-1+y+y^-1) f_6 + f_7`, with
Theorem 3's `h = (1 - z^(1-2t_M))^(d-2)`, `f_1 = (z^t_M + z^(1-t_M)) h`,
`f_2 = z^w h`, `f_3 = z^w (1 + z^(2t_M-1)) h`, `f_4 = z^(w+t_M) h`,
`f_5 = z^w (z^t_M + z^(1-t_M)) h`, `f_6 = h`, `f_7 = z^(2t_M-1)`, as transcribed
in the artifact of `murray-z-only-ansatz-has-no-char0-units`, whose calibration
checks that these are units of `F_d[P]` for `d = 3, 5, 7`. For all 24 cases the
three shadows have norm `1`, shadow C is a monomial, and shadows A and B are not.

**Conclusion.** Item 4 of `promislow-integral-units-have-monomial-definite-line-shadows`
applies to every residue above.

QED
