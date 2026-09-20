---
rg: 2
id: thompson-t-square-central-quotients-no-small-corners-proof
kind: route
title: "Compress, polar-round and spectrally round the corner to an exact pair, tracking each relator and the square-commutator by word length; then the five-step r_2 / r_P identity forces 5 eps_2 + 2 eps_P + 45 gamma >= 2/3 on every nontrivial exact pair"
target: thompson-t-square-central-quotients-have-no-small-corners
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - thompson-t-lochak-schneps-presentation
artifacts:
  - experiments/thompson-t-relator-essentiality-2026-09-17/sl2z_square_central.py
  - experiments/thompson-t-relator-essentiality-2026-09-17/out_sl2z_square_central.json
---

Notation is that of the claim. The words `c, r_1, r_2, r_P` have `L = 6, 20, 34, 10` letters in
`a^(+-1), b^(+-1)` (`sl2z_square_central.py`, key `len c, r1, r2, rP`). All operators below are
contractions, so a product of `L` contractions moves by at most the sum of the letter moves.

This route is self-contained. Part II re-derives inequality (B) of the wave-17 node
`thompson-t-defect-gap-central-square-locus` (held in commit `92b3a78f7d`) in full, so the claim does
not depend on that node landing.

## Part I: the transfer (claim item 1)

Fix an `eps`-corner `P` for `(F, pi)` with `eps < 1/4`. Write `u = pi(a)`, `v = pi(b)`, `H = ran P`,
and `x = P u P|_H`, `y = P v P|_H`.

**Step 1 (compression of words).**
- For a unitary `g`: `P g (1-P) = P [P, g]` and `(1-P) g P = -[P, g] P`. So both have norm
  `<= ||[P, g]||`, and `[P, g^*] = -[P, g]^*` has the same norm. By (C1), every letter
  `g in {u^(+-1), v^(+-1)}` has `||P g (1-P)|| < eps` and `||(1-P) g P|| < eps`.
- Let `w = g_1 ... g_L` be a word. Put `Q_k = (P g_1 P)(P g_2 P) ... (P g_k) g_(k+1) ... g_L P`. Then
  `Q_1 = P pi(w) P`, and `Q_L` is the product of the compressions. Also
  `Q_k - Q_(k+1) = (P g_1 P) ... (P g_k (1-P)) g_(k+1) ... g_L P` has norm `< eps`.
- Hence `||P pi(w) P - w(x, y)|| <= (L-1) eps`. Here the letter `a^(-1)` is sent to
  `P u^* P = x^*`, and similarly for `b^(-1)`.

**Step 2 (polar rounding).**
- `x^* x = P - P u^* (1-P) u P`, so `||x^* x - 1|| <= ||(1-P) u P||^2 < eps^2 < 1`. Hence `x` is
  invertible, and its polar part `U_a` satisfies `||x - U_a|| = || |x| - 1 || <= 1 - sqrt(1 - eps^2) <= eps^2`.
- In the same way, `y` has a polar part `U_b` with `||y - U_b|| <= eps^2`.
- Let `m = 4` for `a` and `m = 3` for `b`. Since `pi(a)^4 = pi(b)^3 = 1`, Step 1 gives
  `||x^4 - 1|| <= 3 eps` and `||y^3 - 1|| <= 2 eps`. So

  ```text
  delta_m := ||U^m - 1|| <= (m-1) eps + m eps^2 < (m - 1 + m/4) eps < 2 m eps.
  ```

**Step 3 (spectral rounding).**
- Let `lambda` be an eigenvalue of `U = U_a` or `U_b`. Write `lambda^m = e^(i phi)` with `|phi| <= pi`.
  Then `2 |sin(phi/2)| <= delta_m`, and `sin t >= 2t/pi` on `[0, pi/2]` gives
  `|phi| <= (pi/2) delta_m < pi m eps`.
- Replace `lambda` by `lambda e^(-i phi/m)`, which is an `m`-th root of unity at distance
  `<= |phi|/m < pi eps` from `lambda`. Doing this in the spectral decomposition of `U` gives a unitary
  `A` with `A^4 = 1` and `||U_a - A|| < pi eps`, and similarly `B` with `B^3 = 1` and `||U_b - B|| < pi eps`.
- So each letter moves by at most `rho := eps^2 + pi eps`: `||x - A|| <= rho` and `||y - B|| <= rho`,
  and the same holds for the adjoints.

**Step 4 (relators and the square-commutator).** For a word `w` of length `L`,

```text
||w(A, B) - 1||  <=  ||w(A,B) - w(x,y)|| + ||w(x,y) - P pi(w) P|| + ||P (pi(w) - 1) P||
                 <=  L rho + (L-1) eps + ||P (pi(w) - 1) P||.
```

Now `L rho + (L-1) eps = L (1 + eps + pi) eps - eps <= (2L + L pi) eps - eps`, since `eps < 1`.
- For `w = r_i`, (C2) bounds the last term by `eps`. This gives `eps_i <= (1 + 2L + L pi) eps`, so
  - `eps_2 <= (69 + 34 pi) eps < 175.9 eps` (`L = 34`);
  - `eps_1 <= (41 + 20 pi) eps` (`L = 20`);
  - `eps_P <= (21 + 10 pi) eps < 52.5 eps` (`L = 10`).

  Hence `D <= 175.9 eps`.
- For `w = c`, the last term is `eta` by definition. Since `c(A, B) = A^2 B A^(-2) B^(-1)`, we have
  `||c(A,B) - 1|| = ||A^2 B - B A^2|| = gamma`. So
  `gamma <= eta + (2·6 + 6 pi) eps - eps < eta + (12 + 6 pi) eps < eta + 30.9 eps`.

**Step 5 (nontriviality).** By (C3), `||x - 1|| >= 1` or `||y - 1|| >= 1`. Then `||A - 1||` or
`||B - 1||` is at least `1 - rho > 1 - 1/16 - pi/4 > 0.15`. So `(A, B)` is a nontrivial exact pair in
`U(rank P)`, in the sense of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`. This proves item 1.

## Part II: the exact-pair inequality (re-derived from wave 17)

**Lemma.** Every nontrivial exact pair `(A, B)`, in every dimension, satisfies
`5 eps_2 + 2 eps_P + 45 gamma >= 2/3`.

*Proof of (B): `||BJ - 1|| <= 5 eps_2 + 2 eps_P + 45 gamma`.* This is the argument of the w17 route.
Each identity below was checked again for this node.

Put `C = BA`, `J = A^2`, so that `J = J^(-1)` and `gamma = ||JB - BJ||`. Each swap of `J` past
`B^(+-1)` costs `gamma`, and `J` commutes with `A`.
1. We have `X = BAB = CB` and `C^(-1) = A^3 B^2 = J A B^2`, so `A B^2 = J C^(-1)`.
2. Put `B' = JBJ`, so that `||B' - B|| = gamma`, `W = J B^2 J = B'^2` and `W^(-1) = J B J = B'`.
   - `Y = W X W^(-1) = B'^2 X B'` lies within `3 gamma` of `Y_0 = B^2 X B = B^3 A B^2 = J C^(-1)`.
   - With `[x, y] = x y x^(-1) y^(-1)`, this gives `||r_2 - [X, Y_0]|| <= 6 gamma`.
   - Next, `[X, Y_0] = CB · J C^(-1) B^(-1) J = CB · J M J` with `M = C^(-1) B^(-1) = A^(-1) B`.
     Then `J M J = A^(-1) B'`, which lies within `gamma` of `M`.
   - So `||r_2 - [C, B]|| <= 7 gamma` and `||CB - BC|| <= eps_2 + 7 gamma`.
3. `B^(-1) C B^(-1) C = A B^(-1) B A = J`. So `B^(-2) C^2 - J = B^(-1) (B^(-1) C - C B^(-1)) C`. Also
   `||B^(-1) C - C B^(-1)|| = ||CB - BC||`. Hence `||C^2 - B^2 J|| <= eps_2 + 7 gamma`.
4. By telescoping, `||C^10 - (B^2 J)^5|| <= 5 eps_2 + 35 gamma`.
   - `(B^2 J)^5 = (B^(-1) J)^5`. Moving the inner `J`'s to the right takes `4+3+2+1 = 10` swaps and
     gives `B^(-5) J^5 = B J`.
   - So `||C^10 - BJ|| <= 5 eps_2 + 45 gamma`.
5. `C^10 = r_P^2`, so `||C^10 - 1|| <= 2 eps_P`. Together with step 4 this gives (B).

*Case analysis.* Put `mu = ||BJ - 1|| = ||B - J||`.
- `J^3 = J` and `B^3 = 1`, so `||J - 1|| = ||J^3 - B^3|| <= 3 mu`.
- **`J != 1`.** Since `J^2 = 1`, `J` has eigenvalue `-1`, so `||J - 1|| = 2` and `mu >= 2/3`. By (B),
  the Lemma holds.
- **`J = 1` and `B != 1`.** `B` has an eigenvalue `e^(+-2 pi i/3)`, so `mu = ||B - 1|| >= sqrt 3`. By (B),
  the Lemma holds.
- **`J = 1` and `B = 1`.** Nontriviality gives `A != 1` with `A^2 = 1`. Then `r_P = A^5 = A`, so
  `eps_P = 2` and `2 eps_P = 4 >= 2/3`.

This proves the Lemma.

## Part III: the corner gap (claim items 2 and 3)

Let `P` be an `eps`-corner with `eps < 1/4`. Apply the Lemma to the exact pair of Part I and insert the
bounds of Step 4:

```text
2/3  <=  5 (69 + 34 pi) eps + 2 (21 + 10 pi) eps + 45 (eta + (12 + 6 pi) eps)
      =  (927 + 460 pi) eps + 45 eta
      <  2373 eps + 45 eta.
```

This is item 2.
- **Square-central `F`.** Here `pi(c) = 1`, so `eta = 0` and `eps > 2/(3 · 2373) = 1/3559.5 > 1/3560`.
- **`eps >= 1/4`.** This case is trivially above `1/3560`.
- **Rearranged.** `eta >= 2/135 - (2373/45) eps > 2/135 - 52.8 eps`, which is the corner form of the
  far-sector condition stated in the claim.

**Item 3.**
- `S = [[0,-1],[1,0]]` and `-ST` satisfy `S^4 = (-ST)^3 = 1` and `S^2 = -1`, and they generate
  `SL(2, Z)`.
- So the pair `(S, -ST)` makes `SL(2, Z)` square-central, and `sl2z_square_central.py` checks all of
  this exactly in integers.
- Every quotient of a square-central group is square-central (the images `a -> S`, `b -> -ST` in
  `SL(2, Z/q)`, and `2I = SL(2,5)`).
- Part III holds for every finite-dimensional unitary representation, with no hypothesis on `|F|`.

**Calibration.**
- The permutation representations of `SL(2, Z/q)` on `(Z/q)^2 \ {0}`, for `q = 3..11`, have
  `gamma = 0` up to `1e-12`, and `D` near 2 (`out_sl2z_square_central.json`).
- This is consistent with the Lemma. Whole representations are far from the bound; the content of the
  node is that no corner of them does better than `1/3560` either.
