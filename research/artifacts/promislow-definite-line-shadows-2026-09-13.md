# Definite dihedral shadows of units on the Promislow group (lane hl-kaplansky-units, 2026-09-13)

This note covers four nodes:
- claim `promislow-integral-units-have-monomial-definite-line-shadows`, route `promislow-definite-line-shadow-parseval-proof`;
- claim `promislow-classical-nontrivial-units-have-no-integral-lifts`, route `promislow-classical-residues-shadow-computation`.

All computation ran on MSI (login node `ahl02`, `/usr/bin/python3.12`, pure
Python, exact integer arithmetic, a few seconds per script), in
`/scratch.global/sauer354/hl-kaplansky-units/run2`. The log is copied verbatim.

| file | md5 |
|---|---|
| `research/artifacts/promislow-definite-shadows-gardam-complex.py` | `6d55ed6877c1c9ff683316897e2bae16` |
| `research/artifacts/promislow-definite-shadows-residues.py` | `03ce7a6e0d5cf47b0a5f9780796cfaf4` |
| `research/artifacts/promislow-definite-shadows-census.py` | `6b83bca2dea80535e46b636faa5de8b6` |
| `research/artifacts/gardam-support-pair-gsp.py` (already on main, imported unchanged) | `1debc5ec75d10b1b92b6e688a385f916` |
| `research/artifacts/promislow-definite-shadows-run-2026-09-13.log` | `0ffb7b000eb9368b6342546b5ed1849c` |
| `census52.json` (MSI, `/scratch.global/sauer354/uc0/t00103/anc`; pinned in `promislow-radius4-support-pairs-zeta8-2026-09-12.md`) | `8f51cffbea19199424772e315aae0a94` |
| `census_pairs.json` (same directory; pinned in `promislow-radius4-census-box-2026-09-13.md`) | `88d50831522fe612ef9412f27237bfb3` |

## 1. The shadows

`D(R) = R[t^(+-1)]<u | u^2 = -1, u f(t) = f(t^-1) u>`, elements `l_0 + l_1 u`,
product `(l_0 + l_1 u)(m_0 + m_1 u) = (l_0 m_0 - l_1 m_1bar) + (l_0 m_1 + l_1 m_0bar) u`,
norm `N = l_0 l_0bar + l_1 l_1bar`.

| shadow | `1, a, b, ab ->` | `x, y, z ->` |
|---|---|---|
| C | `1, u, -t^-1 u, t` | `-1, -1, t^2` |
| A | `1, t, u, t u` | `t^2, -1, -1` |
| B | `1, u, t, t^-1 u` | `-1, t^2, -1` |

`promislow-definite-shadows-gardam-complex.py` gates multiplicativity of each
shadow on 300 random pairs of words of length at most 7 in `a^(+-1), b^(+-1)`
(seed 1), in Gardam's affine model.

## 2. Gardam's complex unit (coefficients in `Z[zeta_8]`, 4-tuples in `Z[s]/(s^4+1)`)

Verbatim from the log (Laurent exponent of `t` as key):

```text
line C | phi(alpha)phi(beta)=1: True | terms in shadow: 7
   l0 = {-3: (2, 0, 0, 0), -1: (-2, 0, 0, 0), 0: (1, 0, 0, 0)}
   l1 = {0: (0, 1, 0, 1), 1: (0, -1, 0, -1), 2: (0, -1, 0, -1), 3: (0, 1, 0, 1)}
   N = l0 l0bar + l1 l1bar = {0: (1, 0, 0, 0)}
line A | phi(alpha)phi(beta)=1: True | terms in shadow: 10
   l0 = {-2: (0, 0, 1, 0), -1: (0, -1, 0, -1), 0: (1, 0, 0, 0), 1: (0, 1, 0, 1), 2: (0, 0, -1, 0)}
   l1 = {-2: (0, 1, 0, 0), -1: (-2, 0, 0, 0), 0: (0, -1, 0, -1), 1: (2, 0, 0, 0), 2: (0, 0, 0, 1)}
   N = l0 l0bar + l1 l1bar = {0: (1, 0, 0, 0)}
line B | phi(alpha)phi(beta)=1: True | terms in shadow: 10
   l0 = {-2: (0, 0, -1, 0), -1: (0, 1, 0, 1), 0: (1, 0, 0, 0), 1: (0, -1, 0, -1), 2: (0, 0, 1, 0)}
   l1 = {-2: (0, -1, 0, 0), -1: (2, 0, 0, 0), 0: (0, 1, 0, 1), 1: (-2, 0, 0, 0), 2: (0, 0, 0, -1)}
   N = l0 l0bar + l1 l1bar = {0: (1, 0, 0, 0)}
```

On line C, `l_0 = 1 - 2t^-1 + 2t^-3` and `l_1 = (zeta_8 + zeta_8^3)(1 - t - t^2 + t^3)`,
with `zeta_8 + zeta_8^3 = i sqrt(2)`. The norm is `1`, but not through a sum of
squares of integers, so the Parseval step of the route does not apply.

## 3. Residues modulo `d`

`promislow-definite-shadows-residues.py`:
- Gardam's unit modulo 2: shadow C `1`; shadows A and B `t^-2 + 1 + t^2 + (t^-2 + t^2) u`,
  norm `1`, and the product with the shadow of the inverse is `1` on every line.
- Murray's Theorem 3 units for `d = 3, 5, 7`, `t_M in {-1, 0, 1, 2}`, `w in {0, 1}`:
  all 24 have norm `1` on every line, a monomial shadow C, and non-monomial
  shadows A and B. First case verbatim (`d = 3, t_M = -1, w = 0`):

```text
  murray line C: l0={-5: 1} l1={} | N={0: 1} | signed monomial: True
  murray line A: l0={-1: 2, 3: 1} l1={-1: 2, 3: 2} | N={0: 1} | signed monomial: False
  murray line B: l0={-1: 2, 3: 1} l1={-3: 2, 1: 2} | N={0: 1} | signed monomial: False
```

## 4. The radius-four census

`promislow-definite-shadows-census.py census52.json census_pairs.json`, verbatim:

```text
rep 0 (orbit size 8): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
rep 1 (orbit size 8): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
rep 2 (orbit size 8): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
rep 3 (orbit size 8): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
rep 4 (orbit size 8): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
rep 5 (orbit size 8): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
rep 6 (orbit size 4): shadows {'C': 'monomial', 'A': 'NOT monomial', 'B': 'NOT monomial'}
52 census units: non-monomial line patterns {('A', 'B'): 52}
units with a non-monomial shadow on some definite line: 52 of 52
DONE
```

Before these lines the script asserts, for every representative pair `(S, T)`,
that the shadows of `sum S` and `sum T` multiply to `1` in both orders and have
norm `1` on every line, and that all 52 residues have norm `1` on every line.

## 5. What is not covered

- **Case A.** A normalized unit `v = 1 mod 2` lies in `+-1 + (I_A cap I_B cap I_C)`
  and is not constrained further. This ideal contains `(x+1)(y+1)(z+1)`.
- **Other residues.** A nontrivial unit of `F_d[P]` whose three shadows are
  monomials is not excluded. None is known: every nontrivial unit checked here
  fails on lines A and B.
- **Other quotients.** The shadows exhaust the lines where the stabilizer in
  `K4` of a character of `L` has order 2 and both squares go to `-1`. On the
  lines with a `+1` the norm is `l_0 l_0bar - l_1 l_1bar` and gives nothing. At
  generic characters the fibre algebra has degree 4 and the reduced norm is not
  a sum of squares.
- **Novelty.** Not searched beyond the sources named in the claims.
