---
rg: 2
id: thompson-t-not-mf-iff-triangle-gap-and-rounding-proof
kind: route
title: Round a small nontrivial pair through the triangle cover, read the relator defect off blockwise, and conclude with the one-gap criterion; kappa_P is constant along conjugation paths of exact pairs
target: thompson-t-not-mf-iff-triangle-gap-and-rounding
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - thompson-t-lochak-schneps-presentation
  - thompson-t-pentagon-winding-sandwich
  - countable-group-mf-conventions
artifacts:
  - experiments/thompson-t-triangle-cover-2026-09-17/gamma2.py
  - experiments/thompson-t-triangle-cover-2026-09-17/out_gamma2.json
---

The notation is that of the target. `||.||` is the operator norm. "Criterion" means
`thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`: `T` is not MF iff some `eps_0 > 0` makes every
`eps_0`-pair trivial, iff `delta_n` does not tend to 0. We use two facts from its proof.

- **(L0a)** A word of length `l` is `l`-Lipschitz in each unitary argument.
- **(L0c)** A nontrivial exact pair has `||A - 1|| >= sqrt 2` or `||B - 1|| >= sqrt 3`.

We also use that the conjugate pair `phi-bar = (A-bar, B-bar)` is an exact pair with
`r(phi-bar) = r(phi)-bar`, so that `||r(phi-bar) - 1|| = ||r(phi) - 1||`. And a word evaluated on a direct
sum is the direct sum of the values, so the defect of a direct sum is the maximum over its summands.

## Item 1 and item 2

**Target ==> (R_Delta).** Take `eps_0` from the criterion. A nontrivial genuine pair `rho` has
`D(rho) = d_T(rho)`, because `r_P(rho) = 1`. If `d_T(rho) < eps_0`, then `rho` is a nontrivial
`eps_0`-pair, which is impossible. So `gamma_n >= eps_0` for all `n`.

**Target ==> (S_T).** Take `delta = eps_0`. Every delta-pair `phi` is `(1,1)`. Then
`phi (+) phi-bar (+) 1_0` is the trivial pair, which is genuine, and it is at distance 0.

**(R_Delta) and (S_T) ==> target.** Suppose the target fails. Put `c = inf_n gamma_n > 0`.
- **Choice of constants.** Choose `eps > 0` with `L eps < c/2` and `eps < 1`. Let `delta` be given by (S_T)
  for this `eps`, and shrink it so that `delta < c/2`.
- **A small pair.** Since the target fails, the criterion gives a nontrivial delta-pair `phi` in some `U(n)`.
- **Rounding.** (S_T) gives a genuine pair `rho` in `U(2n+k)` with `||rho(s) - psi(s)|| < eps`, where
  `psi = phi (+) phi-bar (+) 1_k`.
- **Small defect.** By the direct-sum and conjugation remarks, `d_T(psi) = d_T(phi) < delta`. By (L0a),
  `d_T(rho) <= d_T(psi) + L eps < c`.
- **Nontriviality.** By (L0c), `||psi(a) - 1|| >= sqrt 2` or `||psi(b) - 1|| >= sqrt 3`. So `rho(a) != 1` or
  `rho(b) != 1`, because `eps < 1`.

So `gamma_(2n+k) < c`, a contradiction.

**not (R_Delta) ==> T is MF.** If `inf gamma_n = 0`, there are nontrivial genuine pairs `rho_j` with
`D(rho_j) = d_T(rho_j) -> 0`. So `delta_n -> 0`, and the criterion says that `T` is MF.

**not (S_T) ==> T is MF.** Suppose (S_T) fails for some `eps`. Then for every `delta` there is a delta-pair
that cannot be rounded. It is nontrivial, because a trivial pair rounds to itself. So `delta_n -> 0`, and the
criterion says that `T` is MF.

**(S_T) is automatic in each fixed dimension.** By the criterion `delta_n > 0`. A `delta_n`-pair in `U(n)`
is trivial, so it rounds.

## Item 3 (general form)

The same four arguments work with `Delta` replaced by any finitely presented intermediate quotient
`Gamma`, with `D` in place of `d_T` and the relator lengths of `T` in the Lipschitz bound. For `Gamma = T`,
genuine pairs are trivial by Malcev and simplicity (as in the criterion's proof), so `(R_T)` is vacuous and
`(S_T^T)` says that small pairs are trivial.

## Item 4 (undoubled rounding implies PW)

**Lemma (conjugation path).** Let `(A,B)` be an exact pair and `(A',B')` a genuine pair in `U(N)` with
`||A - A'||, ||B - B'|| <= eps <= 10^(-3)`. Then `kappa_P(A,B) = 0`.

*Proof.*
- **Projections are close.** For a unitary `A` of order 4, the spectral projection for `lambda` is
  `E_lambda(A) = (1/4) sum_(j=0..3) (lambda-bar A)^j`. So `||E_lambda(A) - E_lambda(A')|| <= (1/4)(0+1+2+3) eps = 1.5 eps`.
- **An intertwiner.** Put `z = sum_lambda E_lambda(A) E_lambda(A')`. Then
  `z - 1 = sum_lambda (E_lambda(A) - E_lambda(A')) E_lambda(A')`, so `||z - 1|| <= 1.5 eps · sqrt 4 = 3 eps`
  (Cauchy--Schwarz over the orthogonal `E_lambda(A')`). Also `A z = z A'`.
- **Polar part.** Taking adjoints, `z^* z` commutes with `A'`. So `u = z |z|^(-1)` is unitary, with
  `u A' u^* = A` and `||u - 1|| <= 3·(3 eps) + (3 eps)^2 <= 10 eps`.
- **A genuine pair with the same `A`.** `(A, B'')`, with `B'' = u B' u^*`, is genuine, and
  `||B'' - B|| <= eps + 20 eps = 21 eps`.
- **Second intertwiner.** Repeat the construction for `B` (order 3, with projection bound `1 · 21 eps` and
  factor `sqrt 3`). This gives a unitary `v` with `v B'' v^* = B` and `||v - 1|| <= 3·(37 eps) + (37 eps)^2 <= 113 eps`.
- **The path.** Let `v_t = exp(t log v)` for `t` in `[0,1]`, with principal log. The spectrum of `v` lies in
  a short arc, so `||v_t - 1|| <= ||v - 1||`. Put `B_t = v_t B'' v_t^*`.
  - Every `(A, B_t)` is exact.
  - `||B_t - B''|| <= 226 eps`, so `||(B_t A)^5 - 1|| = ||(B_t A)^5 - (B'' A)^5|| <= 1130 eps < 2`.
- **Constancy.** Along the path `kappa_P(A,B_t) = (1/2 pi i) Tr log (B_t A)^5` is continuous, because the
  spectrum avoids `-1`. It lies in `(1/12) Z` by item 1 of `thompson-t-pentagon-winding-sandwich`. So it is
  constant, and it equals its value 0 at the genuine end `t = 0`. At `t = 1` it is `kappa_P(A,B)`. ∎

**Proof of item 4.** Suppose every delta-pair `phi` has `phi (+) theta` eps-close to a genuine pair, with
`eps <= 10^(-3)`, where `theta` is `1_k` or any genuine pair. Then
`kappa_P(phi (+) theta) = kappa_P(phi) + kappa_P(theta) = kappa_P(phi)`, since the trace of a logarithm is
additive over blocks and `kappa_P(theta) = 0`. By the lemma this is 0. So (PW) holds with this `delta`.

## Item 5

- **Attained.** The genuine pairs in `U(n)` form a compact real-algebraic set. The nontrivial ones form a
  closed subset by (L0c).
- **Positive.** A zero would be a nontrivial homomorphism `T -> U(n)`, by
  `thompson-t-lochak-schneps-presentation`. That is impossible, as in the criterion's proof.
- **Monotone and irreducible form.** Pad with the trivial pair and use the direct-sum remark.
- **`delta_n <= gamma_n`.** A genuine pair is an exact pair with `D = d_T`.
- **`gamma_1 = infinity`.** In the abelianisation, `a^4 = b^3 = 1` and `a^5 b^5 = 1`, so `a = b^(-2) = b`.
  Hence `a` has order dividing `gcd(4,3) = 1`, and `Delta` is perfect.

## Item 6 (`gamma_2`)

**Classification of the 2-dimensional pairs.** Let `rho` be a nontrivial genuine pair in `U(2)`.
- `det rho` is a character of the perfect group `Delta`, so `rho` lands in `SU(2)`.
- If `rho` were reducible, it would be a sum of characters, hence trivial. So `rho` is irreducible.
- If `A` or `B` were central, or `BA = 1`, the image would be abelian. So
  `tr A = 0`, `tr B = -1` and `tr BA = 2 cos(2 pi k/5)` with `k` in `{1, 2}`.
- An irreducible `SU(2)` pair is determined up to conjugacy by `(tr A, tr B, tr BA)`. `gamma2.py` realises
  both triples.

**The image is finite.** In `SO(3)` the images of `A`, `B` and `BA` have orders 2, 3 and 5. So the image
of `rho` in `SO(3)` is a nontrivial quotient of `Delta(2,3,5) = A_5`, hence is `A_5`. The image in `SU(2)`
is therefore the binary icosahedral group `2I`.

**Reading off the values.** The traces of elements of `2I` lie in the finite set
`{±2, ±1, 0, ±(1+sqrt 5)/2, ±(1-sqrt 5)/2}`, whose points are at least 0.38 apart. For `g` in `SU(2)`,
`||g - 1|| = sqrt(2 - tr g)`. `gamma2.py` evaluates `r_1` and `r_2` at 50 digits. It records `sqrt(2 - tr r_i)`, and this identifies each
trace in that finite set exactly (`out_gamma2.json`):
- `tr r_1 = 2` for both `k`, so `r_1 = 1`;
- for `k = 1`, `tr r_2 = (1 - sqrt 5)/2`, so `||r_2 - 1|| = (1 + sqrt 5)/2`;
- for `k = 2`, `tr r_2 = (1 + sqrt 5)/2`, so `||r_2 - 1|| = sqrt((3 - sqrt 5)/2) = (sqrt 5 - 1)/2`.

Hence `gamma_2 = (sqrt 5 - 1)/2 = 2 sin(pi/10)`.
