---
rg: 2
id: soelberg-gardam-unit-has-no-integral-lift-proof
kind: route
title: Relator checks and a parity count show that Gardam's Soelberg unit has non-monomial definite shadows
target: soelberg-gardam-unit-has-no-integral-lift
requires:
  - promislow-integral-units-have-monomial-definite-line-shadows
  - rational-units-rescale-to-integral-units
artifacts:
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_engine.py
  - experiments/soelberg-unit-lifting-2026-09-17/soelberg_definite_shadows.py
  - experiments/soelberg-unit-lifting-2026-09-17/logs/soelberg_definite_shadows.log
---

Notation as in the target. In `D(R)` we use `u f = fbar u`. Every "reflection"
`t^m u` satisfies `(t^m u)^2 = t^m t^-m u^2 = -1`, so `(t^m u)^-1 = -t^m u`.

**Step 1: the shadows are homomorphisms.**

- **`rho_1: x -> t, y -> u`.**
  - `xy -> tu`, a reflection, with square `-1`.
  - `xy^-1 -> t(-u) = -tu`, with square `-1`.
  - So `(xy)^2 (xy^-1)^2 -> (-1)(-1) = 1`.
  - `yx -> ut = t^-1 u`, with square `-1`.
  - `yx^-1 -> u t^-1 = tu`, with square `-1`.
  - So the second relator maps to `1`.
- **`rho_2: x -> u, y -> t`.**
  - `xy -> ut = t^-1 u` and `xy^-1 -> u t^-1 = tu`.
  - `yx -> tu` and `yx^-1 -> -tu`.
  - All four are reflections of square `-1`, so both relators map to `1`.

Both assignments therefore extend to ring homomorphisms `R[S] -> D(R)`. They
are surjective because `rho_1(x^m) = t^m`, `rho_1(x^m y) = t^m u`,
`rho_2(y^m) = t^m` and `rho_2(y^m x) = t^m u`.

**Step 2: classification.** Let `x -> e t^i u^a` and `y -> d t^j u^b` with
`e, d in {+-1}` and `a, b in {0, 1}`.

- **`a = b = 0`.** The image is commutative and cannot span `D(Z)`.
- **`a = b = 1`.** Here `xy -> -ed t^(i-j)` and `xy^-1 -> ed t^(i-j)`, so
  the first relator maps to `t^(4(i-j))`, and `i = j`. The image then lies in
  `{+-1, +-t^i u}` and spans no `t`.
- **`a = 0`, `b = 1`.** Now `xy`, `xy^-1`, `yx` and `yx^-1` are all
  reflections, so both relators hold for every `i`, `j`, `e`, `d`.
  - The span of the image contains `t` only if `i = +-1`.
  - The maps `t -> -t`, `t -> t^-1`, `u -> -u` and `u -> t^k u` are
    automorphisms of `D(Z)` that permute the signed monomials. For the last
    one, `(t^k u)^2 = -1` and `(t^k u) t = t^-1 (t^k u)`.
  - Composing with them normalizes the assignment to `rho_1`.
- **`a = 1`, `b = 0`.** Symmetrically, this normalizes to `rho_2`.

The artifact confirms the count by brute force. Over `|i|, |j| <= 3` it finds
exactly the `112 = 2 * 4 * 14` assignments predicted by the analysis.

**Step 3: units of `D(Z)` are signed monomials.** This is Steps 3 and 4 of
`promislow-definite-line-shadow-parseval-proof`, which use only the ring
`D(Z)`.

- For `X = l_0 + l_1 u`, right multiplication by `X` is left
  `Z[t^(+-1)]`-linear, with matrix `[[l_0, l_1], [-l_1bar, l_0bar]]`.
- So `N(X) = l_0 l_0bar + l_1 l_1bar` is multiplicative.
- If `X` is a unit, `N(X)` is a unit of `Z[t^(+-1)]` invariant under
  `t -> t^-1`, so `N(X) = +-1`.
- The constant term of `N(X)` is the sum of the squares of all coefficients
  of `X`. So `N(X) = 1`, and exactly one coefficient is `+-1`.

**Item 2.** A ring homomorphism sends units to units, so Step 3 gives the
integral statement. For `Q`: `F_p[S]` is a domain for every `p`, since `S` is
torsion-free and elementary amenable (Kropholler--Linnell--Moody, as recorded in
`rational-units-rescale-to-integral-units`). So a unit of `Q[S]` is `c v_0`
with `c in Q^x` and `v_0 in Z[S]^x`.

**Step 4: the images of Gardam's unit.**

- Under `rho_1`, each word of `A` maps to a signed monomial. The table in the
  log lists all 29, for example `A_17 = yxy -> u t u = -t^-1` and
  `A_29 = x^2 y^-1 x^2 y -> 1`.
- Reducing modulo 2 and counting words per monomial gives:

  | monomial | words `A_k` | count |
  |---|---|---|
  | `t` | 1, 13, 18, 28 | 4 |
  | `t^-1` | 2, 16, 17, 26 | 4 |
  | `u` | 3, 4, 12, 15, 25, 27 | 6 |
  | `tu` | 5, 7, 19, 22 | 4 |
  | `t^-1 u` | 6, 9, 20, 21 | 4 |
  | `1` | 8, 10, 29 | 3 |
  | `t^2 u` | 11 | 1 |
  | `t^-2 u` | 14 | 1 |
  | `t^2` | 23 | 1 |
  | `t^-2` | 24 | 1 |

  The counts total 29. The odd counts give
  `rho_1(nu) = 1 + t^2 + t^-2 + t^2 u + t^-2 u`.
- `rho_2(nu)` has the same five terms.
- The script also checks exactly that `rho_1(sum A) rho_1(sum B) = 1` in
  `D(F_2)`, in both orders.
- Well-definedness was cross-checked on 3000 random words in the faithful
  `GL_3(Z)` model: words giving equal group elements have equal shadows, with
  no mismatch.

**Item 3.** Suppose `v in Z[S]^x` reduces to `nu` modulo 2. The shadows are
defined over `Z` and commute with reduction. By Item 2, `rho_1(v) = +-t^m u^e`,
so `rho_1(nu) = t^m u^e` in `D(F_2)`, which contradicts Step 4.

The other residues:

- **Translates.** `rho_1(g nu h) = rho_1(g) rho_1(nu) rho_1(h)`, and
  multiplication by a monomial permutes the basis. So the image still has five
  terms.
- **Automorphic images.** For `alpha in Aut(S)`, `rho_1 o alpha` is a
  homomorphism into the signed monomials with the same spanning image. By
  Step 2 it equals `theta o rho_i`. Then
  `rho_1(alpha(nu)) = theta(rho_i(nu))`, which has five terms because `theta`
  permutes the basis over `F_2`.
- **Inverses.** If `v` reduces to `w^-1`, then `v^-1` reduces to `w`.

For `Z_(2)`, let `v in Z_(2)[S]` be a unit reducing to `nu`. It is a unit of
`Q[S]`, so `v = c v_0` with `v_0 in Z[S]^x` and `c = 2^k c'`, where `c'` is a
2-adic unit.

- The augmentation of `v_0` is `+-1`, so `v_0` has an odd coefficient.
- If `k < 0`, then `v` is not 2-integral.
- If `k > 0`, then `v = 0` modulo 2.
- So `k = 0`, `c = 1` modulo 2, and `v_0` reduces to `nu`, which is
  impossible.

QED
