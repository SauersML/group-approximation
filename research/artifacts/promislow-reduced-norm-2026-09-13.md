# Promislow reduced norm and symmetric-piece units (lane solve-unit-char0-lift, 2026-09-13)

This note covers three nodes:
- `promislow-group-ring-units-are-constant-reduced-norm`
- `promislow-symmetric-piece-units-satisfy-gardam-equations`
- `murray-z-only-shape-has-no-char0-units-any-inverse`

All computation ran on MSI (login node `ahl02`, `/usr/bin/python3.12`, pure
Python, exact integer arithmetic, a few seconds per run), in
`/scratch.global/sauer354/uc0lift/`.

| file | md5 |
|---|---|
| `research/artifacts/promislow-reduced-norm-cp.py` | `bde3676c433d7249830f4b9c52cfceb8` |
| `research/artifacts/promislow-reduced-norm-cp-run.log` (run of 2026-09-13 17:56 CDT) | `ae37dc6e99c37b30d78640e719581f1a` |

## 1. Engine

- **Model.** Gardam's affine model of `P` (arXiv:2312.05240, TeX l.105–120).
  The script asserts both relators, the translations `x, y, z`, and the
  conjugation action.
- **Elements.** An element is `sum_c F_c c` over the representatives
  `1, a, b, ab`, with commutative coefficients.
- **Coefficients.** The coefficients are polynomials in `x^(+-1/2)`,
  `y^(+-1/2)`, `z^(+-1/2)`, with exponents stored doubled, and in symbols `f_g`
  (`g in K4`).
- **Twists.** `sigma_h(f_g) = f_(hg)`. A symbol declared `ab`-invariant is
  canonicalized with `f_C = f_e` and `f_B = f_A`.
- **Product.** `(F c)(G d) = F G^c m(c,d) [cd]`, with the cocycle `m` read off
  the affine model.

**Validations** (log lines `V1`, `V2`):

- `V1`: Tabei's orbit-1 representative and its inverse, typed from
  arXiv:2608.00103 TeX Table 1 (l.268–282).
  - `u u^-1 = u^-1 u = 1` mod 2;
  - `Nrd(u) = 1` mod 2.
- `V2`: Gardam's 2021 unit (arXiv:2102.11818, proof of Theorem A), built from
  his pieces `p0 = vbar wbar (1+z^-1)`, `q0 = v^-2 w^-1 + v^2 w + wbar z`,
  `r0 = vbar + (v^-1 w^-2 + v w^2) z`, `s0 = 1 + (v^-2+v^2+w^-2+w^2) z^-1`
  (`v = x^(1/2)`, `w = y^(1/2)`, `vbar = v + v^-1`) through Lemma 1.
  - `alpha alpha' = alpha' alpha = 1` mod 2;
  - support size 21.
  - The overbars were lost in the PDF extraction. They are restored as the
    unique choice making each piece `ab`-invariant, which Lemma 1 requires.

## 2. Reduced norm (log line `G1`)

`det` of right multiplication on the basis `(1, a, b, ab)`, with
`u = p + q a + r b + s ab` and twists `f^A, f^B, f^C` as independent symbols:
24 terms, `K4`-invariant. This is the verbatim list reproduced in
`promislow-group-ring-units-are-constant-reduced-norm`.

`C2`: `M_(uv) = M_u M_v` for independent symbolic `u`, `v`.

## 3. Symmetric pieces (log lines `L1`, `C1`)

With `P0, Q0, R0, S0` `ab`-invariant symbols and `p = x^(1/2) y^(1/2) P0`,
`q = y^(-1/2) Q0`, `r = x^(1/2) R0`, `s = S0`:

- `(alpha' alpha) = N + M ab` with
  - `N = P0^A P0 - Q0^A Q0 - R0^A R0 + S0^A S0`;
  - `M = x^(-1/2) y^(-1/2) (P0^A S0 - Q0 R0^A + z^-1 (P0 S0^A - Q0^A R0))`.
  The coset-`a` and coset-`b` components are 0, exactly as in Gardam's proof of
  Lemma 1.
- `(alpha alpha') = N + x y M ab`.
- `det M_alpha' = det M_alpha`, a 16-term polynomial.
- `det M_alpha = N^2 - x y z M^2` identically.
- Exponent classes: `N` lies in `Z^3` and `(xyz)^(1/2) M` in `(Z+1/2)^3`,
  computed with the symbol classes `P0: (1/2,1/2,0)`, `Q0: (0,1/2,0)`,
  `R0: (1/2,0,0)`, `S0: (0,0,0)` mod 1.

## 4. Murray shape (log line `C3`)

The pieces from Murray's ansatz with `ab`-invariant symbols `f_1..f_7` are all
`ab`-invariant. The element assembled from them is Murray's `u`, and Gardam's
`alpha'` equals the `u'` of `murray-z-only-ansatz-has-no-char0-units`.

## 5. Sources pinned

- **Tabei, arXiv:2608.00103** (TeX on MSI, `uc0/t00103/main.tex`).
  - l.134–147, "The determinant criterion": credits Craven–Pappas
    (J. Algebra 394 (2013), Thms. 6.8, 8.5, 8.6) and Passman 2021.
  - l.268–282: Table 1.
- **Tabei, arXiv:2608.02982** (PDF via ghostscript on MSI). §1 repeats the
  credit, and §6.1 is the "reduction alone cannot succeed" barrier.
- **Gardam, arXiv:2102.11818** (PDF via ghostscript), p. 6. Lemma 1 and its
  proof table, reconstructed with sub- and superscripts.
- **Gardam, arXiv:2312.05240** (TeX, `uc0/g2312/complex-units.tex`).
  - l.200–210: remarks on the automorphisms `theta_0, theta_1` and on
    [Gardam21, Lemma 1].
  - The complex unit's coefficients are taken from
    `research/artifacts/gardam-support-pair-gsp.py`.

## 6. What this settles and the exact gap

- **Lemma 1 is exact.** For elements with symmetric pieces, Gardam's Lemma 1
  holds as an iff up to a unit constant over every commutative domain. So such
  a unit's inverse is always `N^-1 alpha'`.
- **Murray's shape.** In characteristic 0 it has only trivial units, with no
  assumption on the inverse. This strengthens
  `murray-z-only-ansatz-has-no-char0-units`.
- **Exact gap on this shape.** Over a field of characteristic 0, is there a
  nontrivial solution of `M = 0`, `N in K^x` with symmetric pieces of
  arbitrary `x, y, z`-dependence? Gardam's `F_2` unit and Murray's `F_d` units
  solve it in positive characteristic.
- **Gardam's complex unit is not of this shape** (its coset-1 coefficient is
  not `x^(1/2) y^(1/2)`-symmetric), so the shape is not refuted over `C`.
- **Outside this shape**, the general unit problem over `Q` or `Z` for `P` is
  untouched.
