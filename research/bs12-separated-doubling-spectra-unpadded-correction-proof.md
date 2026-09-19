---
rg: 2
id: bs12-separated-doubling-spectra-unpadded-correction-proof
kind: route
title: Pinch the approximate conjugator along the two spectral decompositions, bound the off-diagonal part by a Wiener-norm Schur multiplier, and take the polar part
target: bs12-separated-doubling-spectra-correct-conjugators-unpadded
requires: []
---

Lane proof (swarm-0917-w12, 2026-09-18), not reviewed.  It is self-contained.
Numerical checks are in `experiments/bs12-fourier-twist-2026-09-17/check_separated_lemma.py`.

**Notation.**  `B' = sum_(y in Y) y P_y`.  Since `Y^2 ⊆ Y`, the operator
`B'^2 = sum_(y in Y) y Q_y` has `Q_y = E_(B')({z in Y : z^2 = y})`, and
`sum_y Q_y = 1`.  Put `R = B'^2 A - A B'`, so that
`||R|| = ||B'^2 - A B' A^*|| <= eta`.

**Step 1 (Sylvester identity).**  For `y, z in Y` we have
`Q_y R P_z = (y - z) Q_y A P_z`.  So for `y != z`,
`Q_y A P_z = Q_y R P_z / (y - z)`.

**Step 2 (Schur multiplier bound).**  Let `theta_0 = 2 arcsin(gamma/2)`, so
`|e^(i theta) - 1| >= gamma` iff `|theta| >= theta_0`.  Also `theta_0 >= gamma`.
Put `c = cot(theta_0/2) <= 2/theta_0`.  Let `kappa` be the odd function on
`(-pi, pi]` that equals `cot(theta/2)` for `|theta| >= theta_0` and
`c theta/theta_0` for `|theta| < theta_0`.  It is continuous, 2pi-periodic
and piecewise `C^1`.  Put `psi(e^(i theta)) = -1/2 - (i/2) kappa(theta)`.
Then `psi(w) = 1/(w-1)` whenever `|w-1| >= gamma`.

Wiener norm.  Write `||f||_2` for the norm in `L^2(d theta/2 pi)`.  Then
`hat psi(0) = -1/2`, and direct integration gives

```text
||kappa||_2^2  <= (1/2pi)(4c + 2c^2 theta_0/3)          <= 16/(3 pi theta_0),
||kappa'||_2^2 <= (1/2pi)(c + c^3/3 + 2c^2/theta_0)      <= (1/2pi)(2/theta_0 + 32/(3 theta_0^3)).
```

Here we used `int_(theta_0)^pi cot^2(t/2) dt <= 2c` and
`int_(theta_0)^pi csc^4(t/2) dt = 2(c + c^3/3)`.  Split the Fourier series at
`L = ceil(1/theta_0)` and apply Cauchy--Schwarz on each side.  With
`sum_(n>L) n^(-2) <= 1/L` this gives

```text
sum_(n != 0) |hat psi(n)| <= sqrt(2L) ||kappa||_2/2 + sqrt(2/L) ||kappa'||_2/2.
```

For `gamma <= 1` we have `theta_0 <= pi/3`, and the two terms are at most
`1.318/theta_0` and `1.012/theta_0`.  So

```text
||psi||_A := sum_n |hat psi(n)| <= 1/2 + 2.33/gamma.
```

Numerically `gamma ||psi||_A` is about `1.576` for `gamma` between `0.003`
and `0.5`.

Now let `Delta(X) = sum_y Q_y X P_y`, which is a contraction, since it is
block diagonal between the two orthogonal decompositions.  Also put
`off(X) = X - Delta(X)`.  For `y != z` in `Y` we have `1/(y-z) = conj(z)
psi(y conj(z))`, because `|y conj(z) - 1| = |y - z| >= gamma`.  Expand
`psi(y conj(z)) = sum_n hat psi(n) y^n conj(z)^n`.  This gives

```text
sum_(y,z) conj(z) psi(y conj(z)) Q_y R P_z
    = sum_n hat psi(n) (sum_y y^n Q_y) R (sum_z conj(z)^(n+1) P_z),
```

and each bracket is a unitary.  The diagonal terms `y = z` carry the
coefficient `conj(y) psi(1) = -conj(y)/2`.  So by Step 1,

```text
off(A) = sum_(y != z) Q_y A P_z
       = [right side above] + (1/2) sum_y conj(y) Q_y R P_y,
||off(A)|| <= (||psi||_A + 1/2) eta <= (1 + 2.33/gamma) eta <= 3.33 eta/g.
```

This covers `gamma <= 1`.  If `gamma > 1`, the set is also `1`-separated, so
apply the bound with `gamma = 1`.

**Step 3 (exact intertwiner).**  `A' = Delta(A)` satisfies
`B'^2 A' = sum_y y Q_y A P_y = A' B'` exactly.  Also
`t := ||A - A'|| <= 3.33 eta/g < 1`, because `7 eta < 2 g`.  So `A'` is
invertible, and its singular values lie in `[1-t, 1+t]`.

Take adjoints in `B'^2 A' = A' B'` and use unitarity.  This gives
`A'^* B'^2 = B' A'^*`, hence `A'^* A' B' = A'^* B'^2 A' = B' A'^* A'`.  So `|A'|`
commutes with `B'`.  Let `C = A' |A'|^(-1)`, which is unitary.  Then

```text
C B' = A' B' |A'|^(-1) = B'^2 A' |A'|^(-1) = B'^2 C,
||C - A|| <= || |A'| - 1 || + ||A' - A|| <= 2t <= 6.66 eta/g <= 7 eta/g.
```

**Step 4 (sharpness).**  Take `A_s, D, W, h` as in the claim.
`W D W^* = D^2`, since `W D e_j = w^j e_(hj)` and `w^(2hj) = w^j`.
`D` has simple spectrum, so every exact `C` has the form `C = W G` with `G`
diagonal.  Put `H = V + V^*`.  Then

```text
||A_s D A_s^* - D^2|| = ||e^(isH) D e^(-isH) - D|| <= s ||[H, D]|| <= 2 s |w - 1| = 2 s gamma.
```

Also `||C - A_s|| = ||G - e^(isH)|| >= ||off(e^(isH))||/2`, because
`off(G) = 0` and `off = 1 - pinching` has norm at most `2`.

By Jacobi--Anger, `e^(isH) = sum_m i^m J_m(2s) V^m`.  So the `(j+1, j)` entry
is `sum_(m == 1 mod N) i^m J_m(2s)`.  The terms with `m != 1` have
`|m| >= N-1` and distinct `|m|`, so

```text
||C - A_s|| >= |J_1(2s)|/2 - sum_(m >= N-1) |J_m(2s)| / 2.
```

In `check_separated_lemma.py`, the pinching correction has `||C - A_s||`
equal to `0.100, 0.1997, 0.4948` at `s = 0.05, 0.1, 0.25` and `N = 45, 135`.
This is within the upper bound `2 M eta` and above the lower bound
`|J_1(2s)|/2`, which is `0.025, 0.050, 0.121`.

**Step 5 (bounded period corollary).**  A point of doubling period `m` is
`e^(2 pi i a/(2^m-1))`.  Two distinct such points with `m, m' <= L` differ
in angle by at least `2 pi/(2^L-1)^2`, hence in chord by at least
`4/(2^L-1)^2`.  The spectral half of `bs12-trivially-padded-opnorm-correction`
gives `||B - B'|| <= c delta` and `eta <= (1 + 3c) delta`.  So `k = 0` and
`epsilon = max(c delta, 7 (1+3c) delta (2^L-1)^2/4)`.
