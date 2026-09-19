---
rg: 2
id: kms-hc1-witt-carry-syzygy-kassel-coordinate-vanishes-proof
kind: route
title: A Fock model computes the seeds, and conjugating by the truncated exponential of E23 turns the integral Heisenberg syzygy into the p-map of a square-zero loop element, whose Kassel part vanishes
target: kms-hc1-witt-carry-syzygy-kassel-coordinate-vanishes
requires: [kms-hc1-ca-edge-defect-is-a-witt-carry-syzygy, kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations]
artifacts:
  - experiments/kms-hc1-kassel-seed-2026-09-18/seed_derive.py
  - experiments/kms-hc1-kassel-seed-2026-09-18/seed_derive.out
  - experiments/kms-hc1-kassel-seed-2026-09-18/fo_seed.cpp
  - experiments/kms-hc1-kassel-seed-2026-09-18/etilde.out
  - experiments/kms-hc1-kassel-seed-2026-09-18/etilde11.out
---

Notation of the target. Fix a prime `p >= 5`. Write `E(x) = sum_(k<p) x^k/k!`.
If `x^p = 0`, then `E(x)` is a unit with inverse `E(-x)`. Write
`eps = E13`, `eps' = E21 t`, `beta = E(b)` and `gamma_j = b^j`. Recall
`1/(p-1)! = -1` and `1/(p-2)! = 1` mod `p`.

## 1. The seeds (S0)

**The Fock model.** In `u(N)`, `n = <a, b, eps>` is a Heisenberg algebra:
`[a,b] = eps`, and `eps` commutes with `a` and `b`. Since `n` meets `H` in
`F a`, PBW gives an injection `u(n)/u(n)a -> M`. The left side has basis
`b^j eps^k m0` with `j, k < p`. On it, `b` and `eps` act by multiplication.
Since `a b^j = b^j a + j b^(j-1) eps` and `a m0 = 0`, the letter `a` acts as
`eps D`, with `D = d/db`.

The multidegree of `b^j eps^k m0` is `(k, j+k, 0)`, and every operator below
raises it. So the component `(2,p,0)` is the coefficient of `eps^2 b^(p-2)`,
and we may compute in `V = F_p[b]/(b^p) (x) F_p[eps]/(eps^3)`.

In `V`, write `A = E(eps D) = 1 + eps D + eps^2 D^2/2` and let `B` be
multiplication by `beta`. As polynomials,
`D beta = beta - b^(p-1)/(p-1)! = beta + gamma_(p-1)`. The other rules are
`D gamma_(p-1) = -gamma_(p-2)`, `beta gamma_(p-1) = gamma_(p-1)`,
`beta gamma_(p-2) = gamma_(p-2) + gamma_(p-1)` and
`beta^(-1) gamma_(p-2) = gamma_(p-2) - gamma_(p-1)`.

As in `fo_dual.cpp`, `r = [a,b,a]` is the word `C^(-1) E(-a) C E(a)`, with
`C = E(-a)E(-b)E(a)E(b)`. So
`rho(r) m0 = B^(-1) A^(-1) B A^(-1) B^(-1) A B A m0`. Apply the factors from
the right, writing `g = gamma_(p-1)` and `h = gamma_(p-2)`.

| factor applied (right to left) | vector |
|---|---|
| `A m0` | `1` |
| `A B` | `beta + eps(beta+g) + eps^2/2 (beta+g-h)` |
| `B^(-1)` | `1 + eps(1+g) + eps^2/2 (1+2g-h)` |
| `A^(-1)` | `1 + eps(1+g) + eps^2/2 (1+2g+h)` |
| `B` | `beta + eps(beta+g) + eps^2/2 (beta+3g+h)` |
| `A^(-1)` | `beta + eps^2 (g+h)` |
| `B^(-1)` | `1 + eps^2 h` |

For example, the fourth row adds `-eps D(eps g) = eps^2 h` to the third. The
sixth row is
`(1 - eps D + eps^2 D^2/2)` applied to the fifth. The `eps` terms cancel. The
`eps^2` coefficient is
`(beta+3g+h)/2 - (beta+g-h) + (beta+g-h)/2 = g + h`. So
`rho(r) m0 - m0 = eps^2 b^(p-2) m0`, and `X_210 = E23^(p-2) E13^2 m0`.

For `[b,c,c]`, `n' = <b, c, eps'>` is Heisenberg with `[b,c] = eps'`. Also
`c m0 = 0` and `c b^j = b^j c - j b^(j-1) eps'`. So `c` acts as `s D`, with
`s = -eps'`. The word is `C^(-1) E(-c) C E(c)` with `C = E(-b)E(-c)E(b)E(c)`.
With `A' = E(sD)`, it gives
`rho(r) m0 = A'^(-1) B^(-1) A' B A'^(-1) B^(-1) A'^(-1) B m0`, since
`E(c) m0 = m0`. The same rules give these vectors, from the right:
`beta - s(beta+g) + s^2/2 (beta+g-h)`, then `1 - s(1+g) + s^2/2 (1+2g-h)`,
then `1 - s(1+g) + s^2/2 (1+2g-3h)`, then `beta - s(beta+g) + s^2/2 (beta-g-3h)`,
then `beta - s^2(g+h)`, then `1 - s^2 h`, and finally `1 - s^2 h`.
So `rho(r) m0 - m0 = -s^2 b^(p-2) m0`, and
`X_012 = -E23^(p-2) (E21 t)^2 m0`. This proves (S0).

`seed_derive.py` runs both products in `V` for `p = 5..31` (`seed_derive.out`).

## 2. The p-map of a degree-1 element

**Lemma.** Let `X` be in `sl_3`, write `X = sum_r c_r E_r + c_A hA + c_B hB`, and
let `tX` be the corresponding element of `N` of `t`-degree 1. Then
`(tX)^[p] = X^p t^p + (c_A^p alpha_A + c_B^p alpha_B) z`.

*Proof.* Expand `(tX)^[p]` with Jacobson's formula, one summand at a time:
`(u+v)^[p] = u^[p] + v^[p] + sum_i s_i(u,v)`, where `u` and `v` are
degree-1 elements. The terms `u^[p]` of the basis summands give the matrix
powers `X_j^p t^p` and the `alpha`-terms. It remains to see that no `s_i`
has a z-part. Write `Y = TU + V`. Then `sum_i i s_i T^(i-1)` is
`(ad (tY))^(p-1)(tU) = [tY, Q]`, with `Q = (ad tY)^(p-2)(tU)`. The element `Q`
has `t`-degree `p-1 < p`, so no cocycle enters it, and
`Q = t^(p-1) (ad Y)^(p-2)(U)` is a loop element. The last bracket pairs degree
1 with degree `p-1`, so its z-part is `kappa tr(Y (ad Y)^(p-2) U)`. That is
`kappa tr(Y [Y, R]) = kappa tr([Y,Y] R) = 0`, with `R = (ad Y)^(p-3) U`,
because `p-2 >= 1`. Since `i < p` is invertible, every `s_i` is a loop
element. The loop parts assemble to `X^p t^p`, because
`x -> x^p` is the restricted structure of `gl_3(F_p[t])` and agrees with
`^[p]` on the basis (`E_r^p = 0` and `h^p = h` for `h = hA, hB`). QED.

## 3. The Kassel coordinate k(p) = 0

**The conjugation.** Let `delta = ad b` on `N (x) F_p[lambda]`. On every
`sl_3 t^k`, `delta^3 = 0`, and `delta z = 0`. The cocycle is `delta`-invariant,
because `b` has `t`-degree 0. So `psi = exp(-lambda delta)`, which has three
terms, is a Lie automorphism: the Leibniz rule only involves `delta^n` with
`n <= 4 < p`. It sends

- `a` to `a~ = a + lambda E13`,
- `c` to `c~ = c - lambda E21 t`,
- `e` to `e~ = e - lambda hB t - lambda^2 E23 t = t (E32 - lambda hB - lambda^2 E23)`.

So `[c~, a~] = e~`, and `e~` commutes with `a~` and `c~`.

**The integral syzygy.** In the enveloping algebra over `Z` of any Lie ring
with `[c,a] = e` and `e` central in `<a,c,e>`, put `v_k = c^(p-k) e^k a^(p-k)`.
The expansion of `a^m c^2` in (S) of the syzygy claim holds over `Z`. It gives
`U1 a^2 = 2v_(p-3) - 9v_(p-2)` and `U2 c^2 = 2v_(p-3) - 9v_(p-2) + 6 v_p`,
with `v_p = e^p`. So `U1 a^2 - U2 c^2 = -6 e^p`.
Reduce mod `p` and substitute `(a~, c~, e~)`, writing `U~_i` for `U_i`
evaluated there. In `u(N)[lambda]`,

```text
U~1 a~^2 - U~2 c~^2 = -6 e~^p = -6 e~^[p].                           (1)
```

**The two sides on m0.** `a E13 = E13 a` and `a m0 = 0`, so
`a~^2 m0 = lambda^2 E13^2 m0`. `[c, E21 t] = 0` and `c m0 = 0`, so
`c~^2 m0 = lambda^2 (E21 t)^2 m0`. The matrix `E32 - lambda hB - lambda^2 E23`
has square 0 and `hB`-coefficient `-lambda`. So by the Lemma,
`e~^[p] = -lambda^p alpha_B z`. Applying (1) to `m0` gives

```text
lambda^2 (U~1 E13^2 - U~2 (E21 t)^2) m0 = 6 lambda^p alpha_B z m0.    (2)
```

**Undoing the conjugation mod lambda^p.** Let `G = E(lambda b)`, a unit of
`u(N)[lambda]`. For any `y`,

```text
G y G^(-1) = sum_(k,l<p) lambda^(k+l) b^k y (-b)^l / (k! l!).
```

Modulo `lambda^p` only `k+l < p` occurs. There,
`sum_(k+l=n) b^k y (-b)^l/(k! l!) = delta^n(y)/n!`. So
`G y G^(-1) = exp(lambda delta) y` mod `lambda^p`. For `y = psi(x)` with `x`
in `N`, this is `x`, because `exp(lambda delta) exp(-lambda delta) = 1` when
`delta^3 = 0`. Hence `G U~_i = U_i G` mod `lambda^p`.

Multiply (2) by `G` and take the coefficient of `lambda^p`. The right side
gives `6 alpha_B z m0`. The left side is the coefficient of `lambda^(p-2)` in
`G (U~1 E13^2 - U~2 (E21 t)^2) m0`, which is also the coefficient of `lambda^(p-2)` in
`(U1 G E13^2 - U2 G (E21 t)^2) m0`. That coefficient is
`(U1 b^(p-2) E13^2 - U2 b^(p-2) (E21 t)^2) m0 / (p-2)!`. Since
`(p-2)! = 1` mod `p`, by (S0) this is `U1 X_210 + U2 X_012`. So

```text
U1 X_210 + U2 X_012 = 6 alpha_B z m0,
```

`zeta(sigma) = 6 alpha_B`, and `k(p) = 0`. QED.

## 4. Checks and remarks

- `etilde.out` (`ETILDE=1 SEEDFORM=1 fo_seed p p 1 p alphaA alphaB`) builds
  `R = -6 sum_(j>=1) b^(p-j)/(p-j)! [lambda^j] e~^p m0` directly by
  straightening. At `p = 5, 7` and `alpha = (0,0), (1,0), (0,1)`, and at
  `p = 11` and `alpha = (0,0), (0,1)` (`etilde11.out`), it prints
  `W - R = 0` with `W = U1 X_210 + U2 X_012`. It also prints `ZETA_SIGMA` equal
  to `6 alpha_B` mod `p`. Here `R` is the right side of the last display
  before the lemma is applied.
- The value `6 alpha_B` agrees with (A) of the syzygy claim, which is now
  unconditional. It also agrees with (K) there at `p = 5, 7, 11, 13`.
- The naive route through divided powers,
  `p(p-1) X_210 = a^2 E23^p m0`, loses exactly the term `-6 z m0`, which is
  torsion. The conjugation by `G` avoids dividing by `p`, because only the
  orders `lambda^j` with `j < p` of `G` are used on the left.
- With (Red) of the syzygy claim, `k(p) = 0 != 2` gives `(E_p)` for every
  `p >= 5`. The remaining gap is the lift of `sigma` to `I` ((S) of the
  syzygy claim), which is argued there and checked at `p = 5, 7`.
