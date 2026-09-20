---
rg: 2
id: mod-s2-tqft-twist-spectra-cube-root-gap-proof
kind: route
title: Spread twist ratios by squared Galois automorphisms, then land exact scalars on the tenth roots by the Maslov line
target: mod-s2-tqft-twist-spectra-obey-the-cube-root-gap
requires:
  - dln-galois-symmetry-of-modular-twists
  - gelaki-nikshych-adjoint-subcategory-is-pointed-centralizer
  - mod-s2-torelli-characters-have-a-metaplectic-maslov-line
---

Notation is that of the target. `||x||` is the distance from `x` to `Z`, and `|e^(2 pi i x) - 1| = 2 sin(pi ||x||)`.

## Step 1: (T1), the unit-square spread

Fix `n >= 2` and `k` with `gcd(k, n) = 1`, and put `x = k/n`. Let `g = max_j ||x j^2||` over units `j` mod `n`.

**Case `n | 24`.**
- For a unit `j` mod `24`, `j^2 = 1` mod `8` and mod `3`, so `j^2 = 1` mod `24`.
- Every unit mod `n` lifts to a unit mod `24`. Hence `j^2 = 1` mod `n`.
- So `g = ||k/n|| >= 1/n >= 1/24`.
- For `(n, k) = (24, +-1)` every value equals `1/24`. This gives equality.

**Case `n` does not divide `24`.** Then some prime power `p^e` exactly divides `n`, with `p >= 5`, or `p = 3` and
`e >= 2`, or `p = 2` and `e >= 4`. Otherwise `n` divides `2^3 3 = 24`.

Write `n = p^e n'` with `gcd(p, n') = 1`. Let `Q` be the set of squares of units mod `p^e`.
- Given `q = j_p^2` in `Q`, use CRT to pick a unit `j` mod `n` with `j = 1` mod `n'` and `j = j_p` mod `p^e`.
- Then `j^2 - 1 = n' t` for an integer `t`, and `n' t = q - 1` mod `p^e`.
- Therefore
  ```text
  x j^2 = x + k t / p^e = x + y_q  mod 1,     y_q = c (q - 1) / p^e,   c = k n'^(-1) a unit mod p^e.
  ```
- Both `x` (take `j = 1`) and `x + y_q` occur among the values. Since `||y_q|| <= ||x|| + ||x + y_q||`,
  ```text
  g  >=  ||y_q|| / 2   for every q in Q.
  ```

It remains to find `q` with `||y_q|| >= 1/10`.
- **`p = 2`, `e >= 4`.** The unit squares mod `2^e` are exactly the residues `= 1` mod `8`: `U = {+-1} x <5>`, and the
  squares are `<25>`, of order `2^(e-3)`. So `q = 1 + 2^(e-1)` is in `Q`. It gives `y_q = c/2` with `c` odd, so
  `||y_q|| = 1/2`.
- **`p = 3`, `e >= 2`.** The group `U(Z/3^e)` is cyclic of order `2 3^(e-1)`. Its squares form its unique subgroup of
  index `2`, which is `{u = 1 mod 3}`. So `q = 1 + 3^(e-1)` is in `Q`. It gives `y_q = c/3` with `3` not dividing `c`,
  so `||y_q|| = 1/3`.
- **`p >= 5`.**
  - `|Q| = s = p^(e-1)(p-1)/2 >= 2`, and `q -> c(q-1)` is injective mod `p^e`.
  - If all `s` values had representatives `r` with `|r| <= R`, then `s <= 2R + 1`. So some value has
    `|r| >= ceil((s-1)/2)`.
  - For `e = 1` the resulting `||y_q||` is at least `1/5` when `p = 5`, `1/7` when `p = 7`, and `(p-3)/(4p) >= 2/11`
    when `p >= 11`.
  - For `e >= 2` it is at least `(p-1)/(4p) - 1/(2 p^e) >= 1/5 - 1/50`.

In every case `||y_q|| >= 1/10`, so `g >= 1/20 > 1/24`. This proves (T1). The script
`experiments/tqft-galois-gap-2026-09-17/unit_square_spread.py` confirms the exact values for `n <= 1200`.

## Step 2: (T2), Galois rigidity

Let `U` be of twist type `(A, L, lambda)`. If `theta` is constant on `L`, every eigenvalue equals `lambda theta_a`,
and `U`, being unitary hence diagonalizable, is that scalar.

Otherwise pick `a, b` in `L` with `theta_a != theta_b`.
- By (DLN0) the twists are roots of unity. So `z = theta_a / theta_b = exp(2 pi i k/n)` with `n >= 2` and
  `gcd(k, n) = 1`.
- By (T1) there is a unit `j` mod `n` with `||k j^2/n|| >= 1/24`.
- Let `sigma_0` be the automorphism of `Q(exp(2 pi i/n))` with `exp(2 pi i/n) -> exp(2 pi i j/n)`, and extend it
  to some `sigma` in `Aut(Q_ab)` (Galois theory of `Q_ab/Q`). Then `sigma^2(z) = z^(j^2)`.
- By the ratio form of (DLN2), `theta_(sigma^ a) / theta_(sigma^ b) = sigma^2(z) = exp(2 pi i k j^2/n)`.
- Since `L` is Galois-stable, `sigma^ a` and `sigma^ b` lie in `L`. So `lambda theta_(sigma^ a)` and
  `lambda theta_(sigma^ b)` are eigenvalues of `U`, and their distance is
  ```text
  |exp(2 pi i k j^2/n) - 1|  =  2 sin(pi ||k j^2/n||)  >=  2 sin(pi/24).
  ```
- `U` is normal, so `||U - mu I||_op = max |alpha - mu|` over eigenvalues `alpha`. For two eigenvalues `alpha, beta`,
  `max(|alpha - mu|, |beta - mu|) >= |alpha - beta|/2`. Hence `||U - mu I||_op >= sin(pi/24)` for every `mu`.

The two alternatives are exclusive, since a scalar has one eigenvalue. This proves (T2).

## Step 3: (T3), the adjoint labels are Galois-stable

Let `A` be pseudounitary with its canonical spherical structure, and let `a` be a simple of `A_ad`.
- By (GN3), `s_(a,u) = s_(a,0)` for every invertible simple `u`. The relation is homogeneous, so it holds for
  `s = rho(s)` of (DLN1), which is a nonzero multiple of the unnormalized S-matrix. The dual-index convention does
  not matter, by the remark at the end of `gelaki-nikshych-adjoint-subcategory-is-pointed-centralizer`.
- Apply `sigma` and the first form of (DLN1), `sigma(s_ij) = eps_sigma(i) s_(sigma^(i) j)`, with `i = a`:
  ```text
  eps_sigma(a) s_(sigma^ a, u)  =  sigma(s_(a,u))  =  sigma(s_(a,0))  =  eps_sigma(a) s_(sigma^ a, 0).
  ```
- Cancel `eps_sigma(a) = +-1`. So `s_(sigma^ a, u) = s_(sigma^ a, 0)` for every invertible `u`, and by (GN3)
  `sigma^ a` lies in `A_ad`.

So `sigma^` maps `Irr(A_ad)` into itself. It is injective, since it is a permutation, and `Irr(A_ad)` is finite. So
`sigma^(Irr(A_ad)) = Irr(A_ad)`. This proves (T3).

## Step 4: (T4), the cube-root gap

Say `U` has property (D) if `U` is scalar or has two eigenvalues at distance at least `2 sin(pi/24)`.

**(D) holds on `T^`.**
- Members of `T` have it by (T2).
- Tensoring with a character `chi` multiplies `rho(t_s)` by the scalar `chi(t_s)`. This preserves scalars and
  distances between eigenvalues.
- For a tensor product, the eigenvalues of `U_1 tensor U_2` are the products `alpha gamma` of eigenvalues. If both
  factors are scalar, so is the product. If `U_1` has eigenvalues `alpha, beta` at distance at least
  `2 sin(pi/24)`, pick any eigenvalue `gamma` of `U_2`. Then `alpha gamma` and `beta gamma` are eigenvalues of the
  product, at the same distance, since `|gamma| = 1`. The case of `U_2` is symmetric.

**Direct sums.** Let `rho = rho_1 + ... + rho_r` with each `rho_i` in `T^`, and let `mu` be in `U(1)`. Then
`||rho(t_s) - mu I||_op = max_i ||rho_i(t_s) - mu I||_op`. Fix any `i`.
- If `rho_i(t_s) = zeta I` is scalar, it commutes with `rho_i(M)`. By (ML3) of
  `mod-s2-torelli-characters-have-a-metaplectic-maslov-line`, `zeta^10 = 1`. So
  `||rho_i(t_s) - mu I|| = |zeta - mu| >= dist(mu, mu_10)`.
- Otherwise, by (D) and the last bullet of Step 2, `||rho_i(t_s) - mu I|| >= sin(pi/24)`.

In both cases the summand is at least `min(sin(pi/24), dist(mu, mu_10))`, which gives the first display.

**At `omega^(+-1)`.**
- `|exp(2 pi i/3) - exp(2 pi i m/10)| = 2 sin(pi ||1/3 - m/10||)`, and `||(10 - 3m)/30|| >= 1/30`, since
  `10 - 3m` is never divisible by `3`. The value `1/30` is attained at `m = 3`. The same holds for `omega^(-1)`.
- So `dist(omega^(+-1), mu_10) = 2 sin(pi/30) ~ 0.2091 > sin(pi/24) ~ 0.1305`, and the minimum is `sin(pi/24)`.

This proves (T4).

## Not part of this route

(T5) is a conditional reading. It is not proved here, and nothing above depends on it.
