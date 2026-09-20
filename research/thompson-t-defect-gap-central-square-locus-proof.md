---
rg: 2
id: thompson-t-defect-gap-central-square-locus-proof
kind: route
title: Rewrite r_2 as the commutator [BA, B] up to 7 gamma, deduce (BA)^2 ~ B^2 A^2, raise to the fifth power against r_P^2, and read off B A^2 ~ 1; in U(2) reduce to one angle and use SU(2) trace identities
target: thompson-t-defect-gap-central-square-locus
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - thompson-gap-witnesses-need-nonamenable-image
artifacts:
  - experiments/thompson-t-defect-census-2026-09-17/dim2_exact.py
  - experiments/thompson-t-defect-census-2026-09-17/out_dim2_exact.json
  - experiments/thompson-t-defect-census-2026-09-17/dim2_lipschitz.py
  - experiments/thompson-t-defect-census-2026-09-17/out_dim2_lipschitz.json
  - experiments/thompson-t-defect-census-2026-09-17/verify_central_j.py
  - experiments/thompson-t-defect-census-2026-09-17/out_verify_central_j.json
---

Notation is that of the claim. `(A, B)` is an exact pair, `C = BA`, `J = A^2`. We use `J^2 = 1`, so
`J = J^(-1)`, and `gamma = ||JB - BJ||`. For unitaries, `||xy - yx|| = ||x y x^(-1) y^(-1) - 1||`, and
products telescope: `||x_1...x_k - y_1...y_k|| <= sum ||x_i - y_i||`.

**Swap costs.**
- `J` commutes with `A`. So `||JC - CJ|| = ||(JB - BJ)A|| = gamma`.
- `||J B^(-1) - B^(-1) J|| = gamma`.
- `||J B^2 - B^2 J|| <= 2 gamma`.

## Part B: the key inequality

**Step 1 (exact identities).**
- `X = BAB = CB`.
- `A = B^(-1) C`, so `A B^2 = A B^(-1) = B^(-1) C B^(-1)`.
- `C^(-1) = A^(-1) B^(-1) = A^3 B^2 = J A B^2`, so `A B^2 = J C^(-1)`.

**Step 2 (`||r_2 - [C,B]|| <= 7 gamma`).** Put `B' = JBJ`, so that `||B' - B|| = gamma`. Then
`W = B'^2` and `W^(-1) = J B^(-2) J = B'`.
- Let `Y = W X W^(-1) = B'^2 X B'` and `Y_0 = B^2 X B = B^3 A B^2 = A B^2 = J C^(-1)`. Then
  `||Y - Y_0|| <= 2 gamma + gamma = 3 gamma`.
- So `||[X,Y] - [X,Y_0]|| <= ||Y - Y_0|| + ||Y^(-1) - Y_0^(-1)|| <= 6 gamma`.
- Next, `[X, Y_0] = CB · JC^(-1) · B^(-1) C^(-1) · C J = C B · (J M J)`, with
  `M = C^(-1) B^(-1) = A^(-1) B`.
- `J` commutes with `A^(-1)`, so `||JMJ - M|| = ||JM - MJ|| = gamma`. Hence
  `||[X, Y_0] - C B C^(-1) B^(-1)|| <= gamma`.
- In total, `||r_2 - [C,B]|| <= 7 gamma`. Therefore

  ```text
  ||CB - BC|| = ||[C,B] - 1|| <= eps_2 + 7 gamma.
  ```

When `J = ±1`, `gamma = 0` and `r_2 = [C, B]` exactly. `verify_central_j.py` confirms this on 20000
random pairs (`rel_I0 ~ 1e-15`).

**Step 3 (`C^2 ~ B^2 J`).** By Step 1, `B^(-1) C B^(-1) C = J C^(-1) C = J`. Hence

```text
B^(-2) C^2 - J = B^(-1) (B^(-1) C - C B^(-1)) C,
```

and `||B^(-1) C - C B^(-1)|| = ||B (B^(-1) C - C B^(-1)) B|| = ||CB - BC||`. So
`||C^2 - B^2 J|| <= eps_2 + 7 gamma`.

**Step 4 (fifth power).**
- Telescoping gives `||C^10 - (B^2 J)^5|| <= 5 eps_2 + 35 gamma`.
- Also `(B^2 J)^5 = (B^(-1) J)^5`. Moving the four inner copies of `J` to the right takes
  `4 + 3 + 2 + 1 = 10` swaps past `B^(-1)`, each of cost `gamma`. The result is
  `B^(-5) J^5 = B J`.
- So `||C^10 - BJ|| <= 5 eps_2 + 45 gamma`.

**Step 5.** `C^10 = r_P^2`, so `||C^10 - 1|| <= 2 eps_P`. Together with Step 4 this gives
**(B)**: `||BJ - 1|| <= 5 eps_2 + 2 eps_P + 45 gamma`.

## Part C: the gaps

Throughout, `5 eps_2 + 2 eps_P <= 7 D`.

**C1 (`J = -1`).** `||BJ - 1|| = ||B + 1||`. The eigenvalues `lambda` of `B` are cube roots of unity,
and `|lambda + 1|` is 2 or 1. So `7 D >= 1`.

**C2 (`J = +1`).**
- If `B != 1`, then `||B - 1|| >= sqrt 3` (L0c of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-proof`),
  so `D >= sqrt(3)/7`.
- If `B = 1`, then `A != 1` and `A^2 = 1`. So `r_P = A^5 = A` and `eps_P = ||A - 1|| = 2`.

**C3 (`gamma = 0`).** `J` commutes with `A` and `B`. So its `±1` eigenspaces reduce the pair, and `D`
is the maximum of `D` over the two blocks. A nontrivial pair has a nontrivial block. On it `J` is the
scalar `±1`, and C1 or C2 gives `D >= 1/7`.

The identification of the locus: `a^2` central gives `b' = a^2 b` with `b'^3 = a^6 b^3 = a^2`. Hence
`G0/<<[a^2,b]>> = <a, b' | a^4, a^2 = b'^3> = Z/4 *_(Z/2) Z/6`, which is `SL(2,Z)`.

**C4 (general).** Put `mu = ||BJ - 1||`.
- `J` is unitary, so `mu = ||(BJ - 1)J|| = ||B - J||`.
- `J^3 = J` and `B^3 = 1`, so `||J - 1|| = ||J^3 - B^3|| <= 3 mu`.
- If `J != 1`, then `J` has eigenvalue `-1` and `||J - 1|| = 2`. So `mu >= 2/3` and, by (B),
  `7 D + 45 gamma >= 2/3`.
- If `J = 1`, then C2 gives `7 D >= sqrt 3 > 2/3`.

(D) is C4 rearranged.

## Part A: `delta_2`

**Reduction.**
- By item (2) of the criterion, `delta_2` is the minimum over nontrivial pairs. Reducible pairs in
  `U(2)` are sums of characters, and those have `D >= delta_1 = 0.5176`.
- An irreducible pair has `A = diag(i^p1, i^p2)` with `p1 < p2`, and `B = Y diag(w^q1, w^q2) Y^*`
  with `q1 < q2`.
- Every `Y` in `U(2)` is `D_1 R(t) D_2`, with `D_i` diagonal unitary and `R(t)` a real rotation. `D_1`
  commutes with `A`, and `D_2` with the diagonal of `B`.
- `R(t) P = R(t + pi/2) diag(1,-1)`, where `P` swaps coordinates. So swapping the eigenvalues of `B`
  is a shift of `t`, and we may fix `q1 < q2`.
- `R(t + pi) = -R(t)`, and `t -> -t` is conjugation by `diag(1,-1)`.
- So `t` may be taken in `[0, pi/2]`. There are 18 profiles `(p, q)`.

**The 17 other profiles (certified numerically).**
- `dB_t/dt = [R' R^T, B_t]` has norm `<= 2`. Among the relators, `r_2` has the most letters `B^(±1)`,
  namely 16.
- So `D(t)` is 32-Lipschitz. On a grid of 16001 points (spacing `h = pi/32000`), the true minimum is
  at least the grid minimum minus `16h = 0.00157`.
- `out_dim2_lipschitz.json`: every profile other than `p = (1,3)`, `q = (1,2)` has a certified lower
  bound `>= 0.51607`. The two lowest are `(0,3),(0,2)` and `(0,1),(0,1)`, at `t = 0`, which are
  characters.

**The minimiser's profile (exact).** Take `p = (1,3)` and `q = (1,2)`, so `A = diag(i, -i)` and
`J = -1`.
- `r_1 = 1` identically, and `A` and `B` are in `SU(2)`.
- `x = tr C = tr(R(t) diag(w, w^2) R(t)^T diag(i, -i)) = -sqrt(3) cos 2t`, which ranges over
  `[-sqrt 3, sqrt 3]`. Write `x = 2 cos phi` with `phi` in `[30°, 150°]`.
- **`eps_2`.** By Part B, Step 2 (`gamma = 0`), `r_2 = [C, B]`. The `SU(2)` trace identity with `tr B = -1` and
  `tr(CB) = tr(B^(-1) A) = tr B^(-1) tr A - tr(BA) = -x` gives `tr r_2 = x^2 - 1`. So
  `eps_2 = sqrt(2 - tr r_2) = sqrt(3 - x^2) = sqrt(3 - 4cos^2 phi)`.
- **`eps_P`.** `C` has eigenvalues `e^(±i phi)`, so `eps_P = 2 |sin(5 phi/2)|`.
- The matrix computation agrees with both formulas, with maximum error `2e-8`, which is the `sqrt`
  near 0.

**Locating the minimum.**
- `eps_2 < 1/2` forces `|cos phi| > 0.829`, that is, `phi < 34.0°` or `phi > 146.0°`.
- On `[30°, 34°]`, `5 phi/2` lies in `[75°, 85°]`, so `eps_P > 1.93`.
- On `[146°, 150°]`, `eps_2` is decreasing and `eps_P = 2 sin(5 phi/2 - 360°)` is increasing. So the
  minimum of `max` is at the crossing `3 - 4c^2 = 2 - 2 cos 5 phi`, where `c = cos phi`.
- With `cos 5 phi = 16c^5 - 20c^3 + 5c`, the crossing condition is `32 c^5 - 40 c^3 - 4c^2 + 10 c + 1 = 0`,
  that is, `x^5 - 5x^3 - x^2 + 5x + 1 = 0` for `x = 2c`.
- The root in range is `x = -1.69649488705...` (`phi = 148.0215603°`, `t = 0.10148606...`). The
  polynomial is irreducible over `Q` (sympy).
- The resultant with `u = 3 - x^2 = delta_2^2` is `u^5 - 5u^4 + 5u^3 + 6u^2 - 9u + 1`. Substituting
  `u = d^2` gives the stated degree-10 polynomial, which sympy also reports irreducible.
- The value `0.349149105985166137...` agrees with the 50-digit mpmath certificate in
  `out_dim2_exact.json`.

**Density.**
- The conjugates of `x` are `-1.697, -1.277, -0.200, 1.130, 2.043`. One of them lies outside
  `[-2, 2]`, so `x` is not `2 cos(2 pi k/m)` and `C` has infinite order.
- The pair is non-abelian, since otherwise `D >= delta_1`.
- A closed infinite proper subgroup of `SU(2)` lies in the normaliser of a torus, which is virtually
  abelian. `thompson-gap-witnesses-need-nonamenable-image` would then give `D >= 1/2`.
- So the closure of the image is `SU(2)`.

## Numerical cross-checks

`verify_central_j.py`, run as `4000 4 3 100`, checks three inequalities:
- (I1) `5 eps_2 + 2 eps_P >= 1` on `J = -1`;
- (I2) the same sum `>= sqrt 3` on `J = +1`, `B != 1`;
- (I3) a *stronger* form of (C4): `5 eps_2 + 2 eps_P + 30 gamma >= 2/3`, with 30 in place of 45.

It uses two tests: 4000 random exact pairs with `n <= 8`, and adversarial Schatten-64 L-BFGS
minimisation of each left-hand side for `n = 2..4`. Results (`out_verify_central_j.json`):

| check | worst ratio of left-hand side to bound |
| --- | --- |
| `r_2 = [C, B]` on `J = ±1` | error `2e-14` |
| (I1) | random 1.035, adversarial 1.039 |
| (I2) | 1.1547, that is, the smallest left-hand side found was 2 |
| (I3) | random 1.55, adversarial 3.00 |

So (I1) is nearly sharp, as a weighted sum. The bound `D >= 1/7` derived from it is not sharp; the
best known value is 0.349. The proof above does not depend on these runs.
