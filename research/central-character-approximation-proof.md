---
rg: 2
id: central-character-approximation-proof
kind: route
title: Approximate a central character by a joint eigenspace in a finite quotient
target: central-quotients-of-residually-finite-groups-are-mf
requires: []
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

## Step 1: central characters are approximable

Write `C = Z(Lambda)`.  Claim: for every character `chi : C -> T` there are
finite-dimensional unitary representations `rho_n` of `Lambda`, each
factoring through a finite quotient, and characters `chi_n` of `C`, with

```text
rho_n(c) = chi_n(c) I  (c in C),      chi_n(c) -> chi(c)  (c in C).  (1)
```

Fix `b_1,...,b_m in C` and `eps > 0`, and choose `N` with `2m/N < eps^2`.
On the abelian `B = <b_1,...,b_m>` let `mu_i` be uniform on
`{b_i^k : 0 <= k < N}` and `mu = mu_1 * ... * mu_m`; repetitions among the
powers are harmless.  Shifting `mu_i` by `b_i` cancels every term but the
two endpoints, and convolution by a probability measure is an
`l^1`-contraction, so

```text
||b_i mu - mu||_(l^1) <= 2/N.                                      (2)
```

Put `F = supp mu`.  Residual finiteness gives a finite quotient
`q : Lambda -> Q` injective on `F union b_1F union ... union b_mF`:
separate each nonidentity quotient of a distinct pair of elements of that
finite set in some finite quotient and take the product.  Define a unit
vector in `l^2(Q)` by

```text
xi(q(x)) = conj(chi(x)) sqrt(mu(x))   (x in F),   xi = 0 elsewhere,
```
well defined by the injectivity.  Then
`(lambda_Q(q(b_i))xi)(q(x)) = xi(q(b_i^-1 x))`, and since
`conj(chi(b_i^-1 x)) = chi(b_i) conj(chi(x))`, the two vectors
`lambda_Q(q(b_i))xi` and `chi(b_i)xi` differ only through the square
roots.  With `(sqrt a - sqrt b)^2 <= |a - b|` and `(2)`,

```text
||lambda_Q(q(b_i))xi - chi(b_i)xi||^2
   <= sum_x |mu(b_i^-1 x) - mu(x)| <= 2/N.                         (3)
```

`q(C)` is a finite central abelian subgroup of `Q`, so its commuting
unitaries on `l^2(Q)` are simultaneously diagonalizable:
`l^2(Q) = (+)_psi E_psi` with `lambda_Q(z)|_(E_psi) = psi(z)I` for
`z in q(C)`.  Each `E_psi` is invariant under all of `Q`, by centrality.
Writing `xi = sum_psi xi_psi` and using orthogonality, `(3)` summed over
`i` gives

```text
sum_psi ||xi_psi||^2 sum_i |psi(q(b_i)) - chi(b_i)|^2 <= 2m/N < eps^2,
```
and the weights `||xi_psi||^2` sum to one, so some `psi` with
`xi_psi != 0` satisfies `|psi(q(b_i)) - chi(b_i)| < eps` for every `i`.

Take `rho = lambda_Q . q` restricted to `E_psi`.  Because `E_psi` is a
joint eigenspace for **all** of `q(C)`, `rho` is scalar on the whole of
`C`, with central character `psi . q`.  Exhausting the countable `C` by
finite sets and taking `eps = 1/n` proves `(1)`.

## Step 2: elements of the image of the centre

Let `g = cZ != 1` with `c in C`.  Characters of a subgroup of a countable
abelian group extend to the whole group, the circle being divisible, so
`C/Z` has a character nontrivial at `cZ`; pull it back to get

```text
chi : C -> T,     chi|_Z = 1,     chi(c) != 1.
```

Choose `rho_n, chi_n` from `(1)`, fix a section `s : G -> Lambda` with
`s(1) = 1`, and put `V_n(x) = rho_n(s(x))`.  For fixed `x,y`,
`z_(x,y) = s(x)s(y)s(xy)^-1` lies in `Z`, hence in `C`, and is central, so
`rho_n(s(x)s(y)) = chi_n(z_(x,y)) rho_n(s(xy))` and

```text
||V_n(x)V_n(y) - V_n(xy)|| = |chi_n(z_(x,y)) - 1| -> |chi(z_(x,y)) - 1| = 0,
```
because `chi|_Z = 1`.  For the chosen `g`, `s(g) in cZ <= C`, so
`V_n(g) = chi_n(s(g))I` and

```text
||V_n(g) - I||_2 = |chi_n(s(g)) - 1| -> |chi(c) - 1| > 0.
```
Both displays are independent of the matrix dimension.

## Step 3: elements outside the image of the centre

Let `g = gamma Z` with `gamma not in C`.  Choose `h` with
`[gamma, h] != 1` and a finite quotient `q` in which that commutator is
still nontrivial.  Then `q(gamma)` is not central in `Q`, while
`q(Z)` is central, so the composite `Lambda -> Q -> Q/Z(Q)` kills `Z` and
factors through `G`, detecting `g`.  Its left regular representation is an
exact finite-dimensional representation `V` of `G`, and a nonidentity
element of a finite group has zero trace there, so
`||V(g) - I||_2^2 = 2`.  The constant sequence `V_n = V` gives `(CQ1)`.

## Step 4: one model for all elements

Enumerate the nonidentity elements as `g_1, g_2, ...` (with repetitions if
`G` is finite), let `W^(j)_k` be a sequence detecting `g_j`, and fix
`delta_j > 0` with `||W^(j)_k(g_j) - I||_2 >= delta_j` for large `k`.
Take an exhaustion `F_n` of `G`; for `j <= n` pick `k(j,n)` large enough
that this separation holds and every multiplicative defect on
`F_n x F_n` is at most `1/n`, and set
`V_n(x) = (+)_(j<=n) W^(j)_(k(j,n))(x)`.  The operator norm of a block
diagonal matrix is the maximum of the block norms, so the multiplicative
errors still vanish, and for `n >= j`,

```text
||V_n(g_j) - I||_op >= ||W^(j)_(k(j,n))(g_j) - I||_op
                    >= ||W^(j)_(k(j,n))(g_j) - I||_2 >= delta_j,
```
using `||A||_2 <= ||A||_op`.  This is `(CQ2)`.  The trivial group is
handled by the one-dimensional representation.
