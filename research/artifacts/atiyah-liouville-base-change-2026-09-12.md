# Base change at Liouville-type coefficients under the determinant conjecture

Lane `ex-atiyah-torsion-free`, 2026-09-12. Supports the claim
`determinant-conjecture-excludes-liouville-atiyah-exceptions`. It sharpens
Theorem 1 of `research/artifacts/atiyah-countable-exceptions-2026-09-12.md`,
where the exceptional set is shown to be countable.

**The problem.** Strong Atiyah over `Qbar` is known to imply Strong Atiyah over
`C` for sofic groups (Jaikin-Zapirain). For other groups this is open
(`strong-atiyah-base-change-algebraic-to-complex`), and the master-host reduction
`algebraic-atiyah-and-determinant-one-group-tester` "gives nothing over `C`".

**What this note proves.** Assume the determinant conjecture and Strong Atiyah
over `Qbar`. Then kernel dimensions stay in the Strong Atiyah lattice at every
complex coefficient vector that algebraic points of bounded degree approximate
faster than any power of their height. Quantitatively, a fractional kernel forces
the coefficients to be Diophantine. The group is never approximated, only the
coefficients.

## 0. Conventions

* `G` is a countable group, and `N(G)` acts on `l^2(G)`.
* For a matrix `A` over `C[G]`, `r_A` is right multiplication, an operator
  between powers of `l^2(G)`. `mu_A` is the spectral measure of `r_A^* r_A` with
  respect to `tau (x) Tr`. If `A` has `n` columns, `mu_A` has total mass `n`.
* `dim ker A := dim_(N(G)) ker r_A = mu_A({0})`.
* Spectral subspaces of `r_A^* r_A` are Hilbert `N(G)`-submodules.
* **Determinant conjecture** `Det(G)`, as in Lueck, arXiv:2102.04549v2 (quoted
  in `master-host-satisfies-determinant-conjecture`): for every matrix `A` over
  `Z[G]`, the Fuglede--Kadison determinant of `r_A`, taken off the kernel, is at
  least `1`. Equivalently,

  ```text
  integral_(0, infinity) log(lambda) d mu_A(lambda)  >=  0.
  ```
* **Strong Atiyah over `Qbar`**, with `L = lcm` of the orders of finite subgroups
  (`L = 1` when `G` is torsion-free): `dim ker A in (1/L) Z` for every matrix `A`
  over `Qbar[G]`.

## 1. Four lemmas

**Lemma 1 (small spectrum under Det).** Let `A` be a matrix over `Z[G]` with `n`
columns, and let `0 < eps < 1`. Then

```text
log(1/eps) * mu_A((0, eps))  <=  n * log+ ||r_A^* r_A||.
```

*Proof.* On `(0, eps)`, `log lambda <= -log(1/eps)`. On `[eps, ||r_A^* r_A||]`,
`log lambda <= log+ ||r_A^* r_A||`, and that set has mass at most `n`. Now add
the two pieces and use `Det(G)`. ∎

**Lemma 2 (min-max).** Let `T` be a bounded `N(G)`-equivariant operator and `W`
a Hilbert `N(G)`-submodule with `||T w||^2 <= eta ||w||^2` for all `w in W`. Then
`dim W <= mu_T([0, eta])`.

*Proof.* `W` meets the spectral subspace `E((eta, infinity))` of `T^* T` only in
`0`. So the orthogonal projection onto `E([0, eta])` is injective on `W`. An
injective equivariant bounded map does not increase von Neumann dimension. ∎

**Lemma 3 (perturbation).** If `||r_A - r_(A')|| <= theta`, then
`dim ker A <= dim ker A' + mu_(A')((0, theta^2])`.

*Proof.* For `v in ker r_A`, `||r_(A') v|| <= theta ||v||`. Apply Lemma 2 with
`W = ker r_A`. ∎

**Lemma 4 (upper semicontinuity).** If `r_(A_k) -> r_A` in norm, then
`dim ker A >= limsup_k dim ker A_k`.

*Proof.* The moments `(tau (x) Tr)((r_(A_k)^* r_(A_k))^j)` converge. The measures
have bounded supports and fixed total mass, so `mu_(A_k) -> mu_A` weakly. For the
closed set `{0}`, weak convergence gives `limsup mu_(A_k)({0}) <= mu_A({0})`. ∎

## 2. Restriction of scalars with a similarity

Let `O ⊂ C` be an order in a number field `L_0` of degree `r`, with Z-basis
`b_1..b_r` and embeddings `sigma_1 = id, sigma_2, ..., sigma_r`. Put
`S = [sigma_j(b_l)]_(j,l)`.

* Multiplication by `b in O` in the basis `b` is an integer matrix `rho(b)`, and
  `rho(b) = S^-1 diag(sigma_j(b)) S`.
* For a matrix `B` over `O[G]` with `n` columns, `rho(B)` is a matrix over `Z[G]`
  with `rn` columns, and

  ```text
  rho(B) = X * Diag * Y,    Diag = diag_j sigma_j(B),    X = S^-1 (x) I,   Y = S (x) I.
  ```

  Here `X` and `Y` are invertible scalar matrices, so they commute with `N(G)`.

**Lemma 5.** Put `kappa = ||S|| ||S^-1||`. For `0 < delta`,

```text
sum_j  mu_(sigma_j(B))((0, delta))  <=  mu_(rho(B))((0, kappa^2 delta]).
```

*Proof.* Let `V` be the spectral subspace of `Diag^* Diag` for `[0, delta)`. It is
the orthogonal sum of the corresponding subspaces of the blocks. For `v in V`,

```text
||rho(B) Y^-1 v|| = ||X Diag v|| <= ||X|| delta^(1/2) ||v|| <= kappa delta^(1/2) ||Y^-1 v||.
```

So Lemma 2 gives `dim Y^-1 V <= mu_(rho(B))([0, kappa^2 delta])`. Also
`ker rho(B) = Y^-1 ker Diag`, so the two kernels have the same dimension.
Subtracting kernels from both sides gives the claim. ∎

**Lemma 6 (a well-conditioned basis).** Suppose `O` is spanned over `Z` by
elements whose conjugates all have absolute value at most `R >= 1`. Then `O` has
a basis with `kappa <= (r^2 R)^r`.

*Proof.*
* **Short basis.** In the Minkowski embedding `O` is a lattice of rank `r`,
  spanned by vectors of length at most `r^(1/2) R`. By the successive minima
  theorem it has a basis of vectors of length at most `r * r^(1/2) R`. So every
  entry of `S` has absolute value at most `r^(3/2) R`, and `||S|| <= r^(5/2) R`.
* **Inverse.** `|det S| = |disc O|^(1/2) >= 1`. The adjugate formula gives
  `||S^-1|| <= r ||S||^(r-1) / |det S|`. Hence
  `kappa <= r ||S||^r <= (r^2 R)^r` for `r >= 2`, and `kappa = 1` for `r = 1`. ∎

## 3. Theorem 2

**Setting.**
* `G` is torsion-free and satisfies `Det(G)` and Strong Atiyah over `Qbar`.
* `F` is a number field, and `A(x) in M_(m x n)(O_F[x][G])` has degree at most
  `D` in the central variable `x`. Clearing denominators by a nonzero integer
  changes no kernel.
* `r = r(A)` is the rank over `D(x)`, and `kappa(z) = dim ker A(z) - (n - r)`.
  This is `>= 0` by the formula of Section 2 of
  `research/artifacts/atiyah-countable-exceptions-2026-09-12.md`.
* For algebraic `xi`, `H(xi)` is the naive height of its primitive minimal
  polynomial over `Z`, and `deg xi = [Q(xi):Q]`.

**Statements.**
1. Only finitely many algebraic `xi` have `kappa(xi) != 0`.
2. Fix `d >= 1`, `R_0 > 0`, and a transcendental `z_0` with `|z_0| <= R_0` and
   `kappa(z_0) > 0`. Then there are `C = C(A, F, d, R_0)` and `c = c(A, F, d, z_0)`,
   both positive, such that

   ```text
   |z_0 - xi|  >=  c * H(xi)^(-C / kappa(z_0))      for every algebraic xi with deg xi <= d.
   ```
3. So no point of the exceptional set `E_G` is algebraically Liouville. Such a
   point would be a transcendental `z_0` for which some `d` and every `K` admit
   algebraic `xi` with `deg xi <= d` and `|z_0 - xi| <= H(xi)^(-K)`.

## 4. Proof of Theorem 2

**Item 1.**
* Write `P A Q = diag(f_i) (+) 0` over `D[x]`, and let `C_i` be the companion
  matrices of the monic parts, as in the countable-exceptions artifact.
* At an algebraic `xi`, `xi - C_i` is a matrix over the skew field `D`, so its
  kernel dimension is an integer.
* The eigenspaces for distinct `xi` are independent in `U(G)^(l_i)`, so at most
  `l_i` algebraic `xi` give a nonzero kernel.

**Item 2.** Let `xi` be algebraic with `deg xi <= d` and `H = H(xi) >= 2`.
Write `C_1, C_2, ...` for positive constants depending only on `(A, F, d, R_0)`.

* **Integral model.** Let `a <= H` be the leading coefficient of the minimal
  polynomial, so `theta = a xi` is an algebraic integer, and put
  `B = a^D A(xi)`, a matrix over `O'[G]` with `O' = O_F[theta]`. `O'` is an order
  in `F(xi)`, of rank `r_0 <= d [F:Q]`.
* **Conditioning.**
  - Every root of the minimal polynomial has absolute value at most `1 + H`
    (Cauchy's bound). So every conjugate of `theta` has absolute value at most
    `2H^2`.
  - `O'` is spanned by the products `omega_l theta^e`, with `omega_l` an integral
    basis of `O_F` and `e < deg theta`. Their conjugates are at most
    `C_1 H^(2d)`.
  - Lemma 6 gives a basis with condition number `kappa_S <= C_2 H^(E_1)`, where
    `E_1` depends only on `d` and `[F:Q]`.
* **Norms.** Each conjugate satisfies `||r_(sigma_j(B))|| <= C_3 H^(3D)`. So
  `||r_(rho(B))|| <= kappa_S * max_j ||r_(sigma_j(B))|| <= C_4 H^(E_2)`.
* **Small spectrum.** Let `0 < t` with `4 kappa_S^2 a^(2D) t < 1`. Since
  `mu_(A(xi))((0, t]) = mu_B((0, a^(2D) t])`, Lemmas 5 and 1 give

  ```text
  mu_(A(xi))((0, t])  <=  mu_(rho(B))((0, 4 kappa_S^2 a^(2D) t))
                     <=  n r_0 * 2 log(C_4 H^(E_2)) / log(1 / (4 kappa_S^2 a^(2D) t))
                     <=  C_5 log H / ( log(1/t) - C_6 log H ).
  ```

* **Perturbation.** For `|z_0 - xi| <= 1`,
  `||r_(A(z_0)) - r_(A(xi))|| <= C_7 |z_0 - xi|`. Lemma 3 gives

  ```text
  dim ker A(z_0)  <=  dim ker A(xi) + mu_(A(xi))((0, C_7^2 |z_0 - xi|^2]).
  ```

* **Removing jumps.** Let `xi_1, ..., xi_q` be the algebraic points of item 1,
  and put `delta_0 = min(1, min_i |z_0 - xi_i|) > 0`. For `xi` outside that list,
  `dim ker A(xi) = n - r`. So for `|z_0 - xi| < 1`,

  ```text
  kappa(z_0)  <=  C_5 log H / ( 2 log(1/|z_0 - xi|) - 2 log C_7 - C_6 log H )
  ```

  whenever the denominator is positive. Rearranging,
  `log(1/|z_0 - xi|) <= (C_5 / (2 kappa(z_0)) + C_6/2) log H + log C_7`.
  Since `kappa(z_0) <= n`, this is at most `(C/kappa(z_0)) log H + log C_7` with
  `C = C_5 + n C_6`. When the denominator is not positive the same bound holds
  trivially. For the listed `xi_i`, and for `|z_0 - xi| >= 1`, the bound holds
  with `c <= delta_0`. This proves item 2.

**Item 3.** An algebraically Liouville `z_0` violates item 2 for any positive
`kappa(z_0)`: take `K > C / kappa(z_0)` and `H` large. So `kappa(z_0) = 0`. By
Theorem 1 of the countable-exceptions artifact, `z_0` is not in `E_A` for any
`A`. ∎

## 5. What it gives, and where it stops

* **Shape of a complex failure.** Let `G` satisfy the determinant conjecture and
  Strong Atiyah over `Qbar`. A matrix over `Qbar(z)[G]` with non-integral kernel
  dimension, or with a kernel jump at a transcendental `z`, needs `z` in a
  countable set of transcendental numbers. Each of those is badly approximable
  by algebraic numbers of every bounded degree, with exponent at most
  `C / kappa`. Liouville numbers, and every `U`-number in Mahler's
  classification, are excluded.
* **At the master host.** By `algebraic-atiyah-and-determinant-one-group-tester`,
  `SA(E)` and `Det(E)` give both hypotheses for every torsion-free group, hence
  this conclusion for every torsion-free group. That node records "Nothing over
  C". This is a first complex-coefficient consequence of the same conjunction.
* **No measure gain.** Almost every complex number is badly approximable in this
  sense, so Theorem 2 adds nothing measure-theoretic to the countability of
  Theorem 1. It adds arithmetic: exceptional values must look like "generic"
  constants such as `e` or `pi`, never like Liouville's constant.
* **Why the box principle does not remove the exceptions.**
  - `serre-class-atoms-obey-degree-bound` excludes transcendental atoms by
    evaluating integer polynomials `p` of degree `l` in a fixed-size integral
    matrix. The gain `l log H` in `log(1/|p(z)|)` beats the cost `log H + l const`.
  - For the companion matrices `C_i` over the skew field `D` needed here, `p(C_i)`
    has no fixed-size integral model. A linear representation of `p(C_i)` over
    `Qbar[G]` has size growing linearly in `l`, so the cost becomes
    `l log H` as well, and the argument gives only a bounded excess, not zero.
* **Not covered.** Algebraic extensions of `Qbar(z)`, as in Section 4 of the
  countable-exceptions artifact.
