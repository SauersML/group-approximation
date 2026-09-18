---
rg: 2
id: qudit-weyl-rounding-constant-triangular-harper-bound-proof
kind: route
title: Stabilizer states see one line of F_d^2, and a chirped Gaussian evaluated by Poisson summation gives the triangular sum frustration 2 sqrt3 pi/d
target: qudit-weyl-rounding-constant-triangular-harper-bound
requires: []
artifacts:
  - experiments/qudit-weyl-rounding-triangular-harper-2026-09-17/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane w3-078, 2026-09-18.

## Setting

- `d >= 5` is prime and `omega = e^(2 pi i/d)`.
- The basis `|x>` of `C^d` is indexed by the representatives `I = {-(d-1)/2, ..., (d-1)/2}` of `Z_d`.
- `Z|x> = omega^x |x>` and `X|x> = |x+1 mod d>`.
- `D(a,b) = omega^(2^(-1) ab) X^a Z^b`, where `2^(-1) = (d+1)/2`, and `T = e^(i pi/d) XZ`.
- Since `omega^((d+1)/2) = -e^(i pi/d)`, we have `T = -D(1,1)`.

The explicit Weyl sum is

```text
K = D(0,1) + D(0,-1) + D(1,0) + D(-1,0) - D(1,1) - D(-1,-1) = Z + Z^* + X + X^* + T + T^*.
```

It has six coefficients of modulus `1`, so `W = 6`. Put `F(psi) = W - <psi|K|psi>` and
`F_min = W - lambda_max(K)`. We show:

- (A) every one-qudit stabilizer state has `<K> <= 2`;
- (B) `F_min <= 2 sqrt3 pi/d + 49 e^(2-d)`.

If some stabilizer state satisfies `<phi|K|phi> >= lambda_max - c (W - lambda_max)`, then by (A)
`2 >= (6 - F_min) - c F_min`, so `c >= 4/F_min - 1`. By (B) this gives the bound in the claim.
Since `2/sqrt3 > 1`, `c_d - d/pi -> infinity`, which refutes `c_d = d/pi + O(1)`.

## (A) Stabilizer value

- A pure one-qudit stabilizer state `phi` is the joint eigenvector of `{D(v) : v in L}` for a line
  `L` of `F_d^2`.
- If `w` is not in `L`, pick `v in L` with symplectic form `[v,w] != 0`. Then
  `D(v)^* D(w) D(v) = omega^t D(w)` with `t != 0`, and `D(v) phi = chi phi` with `|chi| = 1`. So
  `<phi|D(w)|phi> = <phi|D(v)^* D(w) D(v)|phi> = omega^t <phi|D(w)|phi>`, hence
  `<phi|D(w)|phi> = 0`.
- The pairs `{Z, Z^*}`, `{X, X^*}` and `{T, T^*}` lie on the three distinct lines spanned by
  `(0,1)`, `(1,0)` and `(1,1)`. So at most one pair has nonzero expectation, and that pair
  contributes at most `2`.
- Hence `<K> <= 2`, with equality at `|0>`.

## (B) The chirped Gaussian

Take real `a > 0` and `b`, and put `alpha = 2a/d` and `g(t) = exp(-pi (a - ib) t^2/d)`. Let
`psi = sum_(x in I) g(x) |x>`, not normalized. Its squared norm is
`N_I = sum_(x in I) e^(-pi alpha x^2)`. Directly from the definitions:

```text
<psi|Z|psi> = sum_(x in I) omega^x e^(-pi alpha x^2),
<psi|X|psi> = sum_(x in Z_d) conj(psi(x)) psi(x-1),
<psi|T|psi> = e^(i pi/d) sum_y conj(psi(y+1)) omega^y psi(y) = e^(-i pi/d) sum_(x in Z_d) omega^x conj(psi(x)) psi(x-1).
```

`omega^x` depends only on `x mod d`, so the only effect of the cyclic structure is one wrap-around
term in the `X` and `T` sums, the pair `x = -(d-1)/2`, `x - 1 = (d-1)/2`.

**Full-lattice sums.** Put `S_0 = sum_(x in Z) e^(-pi alpha x^2)` and `S_u = sum_(x in Z) h_u(x)`, where
`h_Z(x) = omega^x e^(-pi alpha x^2)`, `h_X(x) = conj g(x) g(x-1)` and `h_T(x) = e^(-i pi/d) omega^x h_X(x)`.
Expanding the exponent,
`conj g(x) g(x-1) = e^(-pi(a-ib)/d) exp(-pi alpha x^2 + 2 pi(a - ib) x/d)`. So every
`h_u(x) = k_u exp(-pi alpha x^2 + 2 pi i beta_u x)` with:

| `u` | `k_u` | `beta_u` |
|---|---|---|
| `Z` | `1` | `1/d` |
| `X` | `e^(-pi(a-ib)/d)` | `-(b + ia)/d` |
| `T` | `e^(-i pi/d) e^(-pi(a-ib)/d)` | `(1 - b - ia)/d` |

**Poisson summation.** For `alpha > 0` and complex `beta`,
`sum_(x in Z) e^(-pi alpha x^2 + 2 pi i beta x) = alpha^(-1/2) sum_(m in Z) e^(-pi (m - beta)^2/alpha)`.
This holds for real `beta` by Poisson summation, and for complex `beta` because both sides are entire in `beta`.

*The m = 0 term* is `alpha^(-1/2) k_u e^(-pi beta_u^2/alpha)`. With `pi/alpha = pi d/(2a)`:
- `Z`: exponent `-pi/(2ad)`.
- `X`: `-pi(a - ib)/d - pi(b^2 - a^2 + 2iab)/(2ad)`. The real part is `-pi(a^2 + b^2)/(2ad)`, and the
  imaginary part is `pi b/d - pi b/d = 0`.
- `T`: `-i pi/d - pi(a - ib)/d - pi((1-b)^2 - a^2 - 2ia(1-b))/(2ad)`. The real part is
  `-pi(a^2 + (1-b)^2)/(2ad)`, and the imaginary part is `(-pi + pi b + pi(1-b))/d = 0`.

So the main terms are `alpha^(-1/2) e^(-x_u)`, with real
`x_Z = pi/(2ad)`, `x_X = pi(a^2+b^2)/(2ad)` and `x_T = pi(a^2+(1-b)^2)/(2ad)`.

*The m != 0 terms.* Relative to the main term they have modulus
`e^(-pi Re((m-beta)^2 - beta^2)/alpha) = e^(-pi (m^2 - 2m Re beta)/alpha)`. Here `|Re beta_u| <= 1/d`,
so `m^2 - 2|m|/d >= m^2 (1 - 2/d)`, and their total is at most
`2 sum_(m>=1) e^(-pi m^2 (d-2)/(2a))`. From now on `a = sqrt3/2` and `b = 1/2`. Then this is at
most `2.01 sigma`, with `sigma = e^(-pi (d-2)/sqrt3)`, since `pi(d-2)/sqrt3 >= 5.4` for `d >= 5`.
Hence `S_u = alpha^(-1/2) e^(-x_u)(1 + mu_u)` with `|mu_u| <= 2.01 sigma`, and
`S_0 = alpha^(-1/2)(1 + mu_0)` with `0 <= mu_0 <= 2.01 sigma`.

**Truncation.** Now `alpha = sqrt3/d` and `pi alpha d = pi sqrt3 >= 5.4`. Put
`tau = e^(-pi alpha (d-1)^2/4) = e^(-pi sqrt3 (d-1)^2/(4d))`.
- `S_0 - N_I` and `S_Z - <psi|Z|psi>` are sums over `|x| >= (d+1)/2` of terms of modulus
  `e^(-pi alpha x^2)`, so their moduli are at most `2 e^(-pi alpha (d+1)^2/4)/(1 - e^(-pi alpha d)) <= 2.01 tau`.
- For `X` and `T`, `|h_u(x)| = e^(-pi alpha (x^2 + (x-1)^2)/2) <= e^(-pi alpha (x - 1/2)^2)`.
  - The integers `x` for which `x` and `x - 1` are not both in `I` have `|x - 1/2| >= d/2`. They
    contribute at most `2.01 tau`.
  - The wrap-around term has modulus `e^(-pi alpha (d-1)^2/4) = tau`.
  - So `|S_u - <psi|u|psi>| <= 3.01 tau`.

**Assembly.** For `d >= 5`, `x_u <= pi/(sqrt3 d) < 0.37` and `alpha^(-1/2) >= 1.6`. Also
`sigma, tau < 0.02`, so `Re <psi|u|psi> > 0`. Since `N_I <= S_0` and `alpha <= 1`,

```text
Re<u>  =  Re<psi|u|psi>/N_I  >=  (alpha^(-1/2) e^(-x_u)(1 - 2.01 sigma) - 3.01 tau) / (alpha^(-1/2)(1 + 2.01 sigma))
       >=  e^(-x_u)(1 - 4.02 sigma) - 3.01 tau  >=  1 - x_u - 4.02 sigma - 4 tau,
```

using `1 - e^(-x) <= x`. With `a = sqrt3/2` and `b = 1/2`, all three `x_u` equal
`pi/(sqrt3 d)`. The six terms of `K` come in conjugate pairs with equal real parts, so

```text
F(psi)  =  2 sum_(u in {Z,X,T}) (1 - Re<u>)  <=  6 pi/(sqrt3 d) + 25 sigma + 24 tau  =  2 sqrt3 pi/d + 25 sigma + 24 tau.
```

Finally, `pi(d-2)/sqrt3 >= d - 2` and `pi sqrt3 (d-1)^2/(4d) >= 1.36 (d-2)`, so
`25 sigma + 24 tau <= 49 e^(2-d)`. Hence `F_min <= F(psi) <= 2 sqrt3 pi/d + 49 e^(2-d)`. This proves
(B), and with (A) the claim.

## Remarks

- The choice `a = sqrt3/2`, `b = 1/2` minimizes the main term `(pi/(ad))(1 + 2a^2 + b^2 + (1-b)^2)`
  over `(a,b)`. Semiclassically `psi` is the Gaussian ground state of `Q^2 + P^2 + (Q-P)^2`.
- With `+D(1,1)` in place of `T` the three phases are frustrated. The ground energy is then of order
  `1`, and the ratio is about `0.2` (`tri_quick.log`, sign `+1`).
- The error bound is crude; at `d = 5` it exceeds the main term. The numerics
  (`gauss_trial.log`) show `F(psi) <= 2 sqrt3 pi/d` for every tested `d`, and
  `F(psi) - F_min <= 4e-4`. They also show the exact ratio `4/F_min - 1` above `2d/(sqrt3 pi) - 1`
  for `d = 5, ..., 401`. The proof does not use them.
- The same computation for the square Harper sum `Z + Z^* + X + X^*` (`a = 1`, `b = 0`, main term `pi(1 + a^2 + b^2)/(ad)`) gives
  `F_min <= 2pi/d + O(e^(-cd))`. Since `W = 4` and `F_stab = 2`, this gives `c_d >= d/pi - 1 - o(1)`. That makes the Harper lower
  bound of `qudit-weyl-rounding-sharp-constant` rigorous, where it had been only numerical.
