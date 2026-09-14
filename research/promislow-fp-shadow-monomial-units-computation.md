---
rg: 2
id: promislow-fp-shadow-monomial-units-computation
kind: route
title: Twist Gardam's unit by diagonal automorphisms and commute Murray's units with z, with exact shadows and triviality tests
target: promislow-fp-has-nontrivial-shadow-monomial-units
requires:
  - promislow-integral-units-have-monomial-definite-line-shadows
  - promislow-classical-nontrivial-units-have-no-integral-lifts
  - unit-conjecture-fails-over-complex-numbers
  - murray-z-only-ansatz-has-no-char0-units
---

**Step 1: diagonal automorphisms.** In Gardam's affine model an element of `P` is
`v -> D v + t`, with `D` the linear part of one of `1, a, b, ab` and
`t = t_c mod 2 Z^3`, where `t_c` is the translation of that representative
(`L` is the group of translations by `2 Z^3`). Let `h = diag(e_1, e_2, e_3)`.

- Diagonal matrices commute, so `h (D, t) h^-1 = (D, h t)`.
- Since `h t = t mod 2 Z^3`, the image lies in `P`.
- So conjugation by `h` is an involutive endomorphism of `P`, hence an
  automorphism `sigma_h`.

**Step 2: item 1 (`p = 2`).** The script
`research/artifacts/promislow-shadow-twisted-units.py` loads
`research/artifacts/promislow-definite-shadows-residues.py`, which loads
`research/artifacts/gardam-support-pair-gsp.py`. Those rebuild Gardam's unit
`alpha` and inverse `beta` over `Z[s,t]/(s^4+1, t^4+1)` and check
`alpha beta = beta alpha = 1`. Every coefficient is `+-s^i t^j`, so the reductions
`u`, `u'` modulo 2 are the sums of the supports.

The script checks, exactly in `F_2[P]`:

- `u u' = 1`;
- for each of the seven `h != 1`, `v_h = u sigma_h(u')` satisfies
  `v_h sigma_h(u) = u`, so `v_h` is a unit;
- the three shadows of `v_h`, computed from its coefficients, and also as
  `shadow(u) shadow(sigma_h(u))^-1` in `D(F_2)`;
- whether `u = lambda g sigma_h(u)` for some `g in P` (triviality).

Log `research/artifacts/promislow-shadow-twisted-units-run-2026-09-13.log`,
md5 `5ad8440eedb525cf28ebf0a003eec132`:

| `h`          | `supp v_h` | unit | monomial `C, A, B` | nontrivial |
|--------------|------------|------|--------------------|------------|
| `(1,1,-1)`   | 109 | True | True, True, True  | True |
| `(1,-1,1)`   | 81  | True | True, True, False | True |
| `(1,-1,-1)`  | 161 | True | True, True, False | True |
| `(-1,1,1)`   | 61  | True | True, True, True  | True |
| `(-1,1,-1)`  | 73  | True | True, True, True  | True |
| `(-1,-1,1)`  | 61  | True | True, True, False | True |
| `(-1,-1,-1)` | 165 | True | True, True, False | True |

**Step 3: item 2 (`p = 3, 5, 7`), commutators.** Murray's units are units of
`F_p[P]` for `p = 3, 5, 7`. That is the calibration of
`murray-z-only-ansatz-has-no-char0-units`, and the formulas are those of
`promislow-classical-residues-shadow-computation`. The same route computes that
the shadow on line `C` of each of the 24 cases is a signed monomial
`epsilon t^m` or `epsilon t^m u`.

By the table of `promislow-integral-units-have-monomial-definite-line-shadows`,
`z = (ab)^2` maps to `t^2` on `C` and to `-1` on `A` and `B`. Shadows are ring
homomorphisms, so:

- **Lines `A, B`.** `shadow([u, z]) = X (-1) X^-1 (-1)^-1 = 1`.
- **Line `C`.** `shadow([u, z]) = m t^2 m^-1 t^-2` with `m` a signed monomial.
  If `m = epsilon t^k`, this is `1`. If `m = epsilon t^k u`, then
  `u t^2 u^-1 = t^-2`, so it is `t^-4`.

So `[u, z]` has monomial shadows. `[u, z]` is a trivial unit iff
`u z = lambda k z u` for some `k in P`, `lambda in F_p^x`.

The script `research/artifacts/promislow-shadow-twisted-units-odd.py` tests this
exactly for all 24 cases and finds no such `k`. It also recomputes the commutator
shadows in `D(F_p)`. Log
`research/artifacts/promislow-shadow-twisted-units-odd-run-2026-09-13.log`, md5
`e35a5fe9666adf434554b682fb7a5d1a`: `d=3,5,7: 48 commutators, 8 hits` each. The
8 hits are exactly `g = z` for all eight parameter pairs.

**Step 4: item 2, quotients.** The same script forms the 64 elements
`sigma_h(u_i)`: 8 parameter pairs, and 8 signs `h` including `h = 1`. For each of
the 4032 ordered pairs `(w_1, w_2)` it checks in `D(F_p)` whether all three
shadows of `w_1 w_2^-1` are monomials. When they are, it tests exactly whether
`w_1 = lambda g w_2`. Log: `d=3,5,7: 4032 ordered quotient pairs, 384 hits` each.
A unit that is not `lambda g` is nontrivial.

**Script md5s:**
- `promislow-shadow-twisted-units.py` `302d0ec30ea3c39458a8b7a42ca254fe`
- `promislow-shadow-twisted-units-odd.py` `8a8a94d67713b6bda38acdff62045572`
- `promislow-definite-shadows-residues.py` `03ce7a6e0d5cf47b0a5f9780796cfaf4`
- `gardam-support-pair-gsp.py` `1debc5ec75d10b1b92b6e688a385f916`

All were run on MSI with Python 3.12.

QED
