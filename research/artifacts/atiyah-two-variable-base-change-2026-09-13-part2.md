# Two transcendental coefficients under the determinant conjecture, part 2

Lane `ex2-atiyah-base-change-td2`, 2026-09-13. Continues Part 1 and uses its
output `M = M_0 + x_1 M_1 + x_2 M_2`, `kappa_0 >= 1`, `Y`. **Unreviewed.**

## 3. The integral model of a zero-dimensional cycle

Let `Z` be an irreducible zero-dimensional cycle over `Q` in `A^2`: the Galois
orbit of `zeta in Qbar^2`, of degree `D = [K : Q]`, `K = Q(zeta_1, zeta_2)`,
with embeddings `sigma_1, ..., sigma_D`.

* `Lambda_k ⊂ K` is the `Z`-span of the monomials `zeta^alpha` with
  `|alpha| <= k`. For `k >= D - 1` it is a lattice of rank `D`.
* `ev: K (x) C -> C^D` sends `f` to `(sigma_j f)_j`. It is an isomorphism.
* In `Z`-bases of `Lambda_k` and `Lambda_(k+1)`, let `A_0` be the matrix of the
  inclusion and `A_i` (`i = 1, 2`) the matrix of multiplication by `zeta_i`.
  All three are integer `D x D` matrices.

**Lemma G (resultant identity for cycles).** Put
`X_k = M_0 (x) A_0 + M_1 (x) A_1 + M_2 (x) A_2 in M_(ND)(Z[G])`. If no
`sigma_j zeta` lies in `Y`, then `X_k` is injective and

```text
Delta(X_k)  =  [Lambda_(k+1) : Lambda_k]^N  prod_(j=1..D) Delta(M(sigma_j zeta)).          (RES2)
```

*Proof.* Let `E_k`, `E_(k+1)` be the matrices of `ev` on the two bases. Then
`E_(k+1) A_i = diag(sigma_j zeta_i) E_k` for `i = 1, 2`, and
`E_(k+1) A_0 = E_k`. So

```text
(I_N (x) E_(k+1)) X_k  =  ((+)_j M(sigma_j zeta)) (I_N (x) E_k).
```

The blocks are injective by the choice of `Y`, so `X_k` is injective.
(D1)-(D3) give
`Delta(X_k) |det E_(k+1)|^N = prod_j Delta(M(sigma_j zeta)) |det E_k|^N`. Also
`det E_k = det E_(k+1) det A_0`, and `|det A_0| = [Lambda_(k+1) : Lambda_k]`. ∎

For `Z = V(p)` in one variable this is (RES), with `[Lambda_(k+1):Lambda_k] = |a|`.

**Lemma H (the index is the finite height).** Let
`h_fin(Z) = sum_p sum_(w | p) [K_w : Q_p] log max(1, |zeta_1|_w, |zeta_2|_w)`.
There are `E >= 1` and `k_1` such that
`log [Lambda_(k+E) : Lambda_k] = E h_fin(Z)` for all `k >= k_1`. Also
`h_fin(Z) = log |c_Z|`, where `F_Z = c_Z prod_j (u_0 + u_1 sigma_j zeta_1 + u_2 sigma_j zeta_2)`
is the primitive integral Chow form of `Z`.

*Proof.*
* **Almost all primes.** Put `k_0 = max(1, D-1)`, so that `Lambda_(k_0)` has
  rank `D` and contains `1, zeta_1, zeta_2`. `Lambda_(k_0) (x) Z_p = O_K (x) Z_p`
  for all but finitely many `p`. For those `p` the `zeta_i` are `p`-integral, so
  `Lambda_(k,p)` is constant for `k >= k_0` and `h_fin` has no `p`-part. Let `S`
  be the finite set of the other primes.
  *(Corrected by ex-verify2-quantum-l2, 2026-09-13. The text used `D-1` in place
  of `k_0`. For `D = 1`, `Lambda_0 = Z` does not see the denominators of a
  rational point: see the model test `Z = {(1/2, 1/3)}` in Part 3 §6.)*
* **Normalization at `p in S`.** Put `O'_p = prod_(w|p) O_w`. For each `w | p`,
  pick `varpi_w in {1, zeta_1^-1, zeta_2^-1}` with
  `|varpi_w|_w = pi_w^-1`, `pi_w := max(1, |zeta_1|_w, |zeta_2|_w)`. Then
  `L_k := varpi^k Lambda_(k,p) ⊂ O'_p` is a full lattice.
* **A unit-valued form.** The points `xi_w = varpi_w (1, zeta_1, zeta_2)` have
  primitive reductions in `P^2(F_q)` for some `q = p^f`.
  - Let `theta` generate `F_(q^3)` over `F_q`. The norm form
    `N_(F_(q^3)/F_p)(x_0 + x_1 theta + x_2 theta^2)` is a form over `F_p` with no
    nontrivial zero in `F_q^3`.
  - Lift it to `G in Z[x_0, x_1, x_2]`, of degree `e_p`. Put `g(x) = G(1, x)`.
    Then `varpi_w^(e_p) g(zeta) = G(xi_w)` is a unit at every `w | p`.
* **Monotone index.** `g Lambda_k ⊂ Lambda_(k+e_p)`, so
  `G(xi) L_k ⊂ L_(k+e_p)`. Multiplying by a unit of `O'_p` preserves the index
  in `O'_p`. So `[O'_p : L_k]` is a non-increasing positive integer along each
  residue class mod `e_p`, hence eventually constant.
* **Index.** Once it is constant,
  `[Lambda_(k+e_p,p) : Lambda_(k,p)] = [varpi^-(k+e_p) O'_p : varpi^-k O'_p] = prod_(w|p) pi_w^(e_p [K_w:Q_p])`.
  Take `E = lcm_(p in S) e_p` and multiply over the primes.
* **Gauss.** The Gauss norm at `p` is multiplicative and `F_Z` is primitive.
  So `|c_Z|_p prod_(w|p) pi_w^([K_w:Q_p]) = 1` for every `p`. Summing logs over
  `p` gives `h_fin(Z) = log |c_Z|`. ∎

**Proposition C (the determinant conjecture on cycles).** If `Z ∩ Y = ∅`, then

```text
sum_(j=1..D) log Delta(M(sigma_j zeta))  +  N h_fin(Z)  >=  0.
```

*Proof.* `Delta(X_k) >= 1` by the determinant conjecture. Take logs in (RES2)
for `k, k+1, ..., k+E-1`, add, and apply Lemma H. ∎

## 4. Chow quantities and the basic inequality

Put `theta~ = (1, z_1, z_2)`. For `u, v in C^3`, `u . v` is the bilinear dot
product and `u x v` the bilinear cross product. `M(P)` is the Mahler measure on
the torus `T^3`. We use:
- **(M1)** `M` is multiplicative;
- **(M2)** `M(P) >= 1` for nonzero `P in Z[u]`;
- **(M3)** `max_i |w_i| <= M(w . v) <= ||w||` for linear forms;
- **(M4)** `M(P) <= sup_(T^3) |P|`.

For an integral form `F(u) = c prod_j (u . zeta~_j)` with `zeta~_j = (1, zeta_j)`
and `c = F(1,0,0) != 0` (all points affine), put

```text
a(F) = log M( v -> F(theta~ x v) ),        b(F) = log M(F).
```

Since `F(theta~ x v) = c prod_j v . (zeta~_j x theta~)`, (M1) and (M3) give the
estimates below. Also `zeta~ x theta~ = (zeta_1 z_2 - zeta_2 z_1, zeta_2 - z_2, z_1 - zeta_1)`,
so `||zeta~ x theta~|| >= ||zeta - z||`. Hence

```text
sum_j log ||zeta_j - z||           <=  a(F) - log|c| + D log sqrt3,
sum_j log max(1, ||zeta_j||)       <=  b(F) - log|c| + D log sqrt2.
```

**Upper bound (UB2).** With `c_M = max(||M_0||, ||M_1||, ||M_2||, 1)`, for every
`w in C^2`:
`log Delta(M(w)) <= kappa_0 log(2 c_M ||w - z||) + (N - kappa_0) log(3 c_M max(1, ||w||))`.
The proof of (UB) applies verbatim, since `||M(w) - M(z)|| <= 2 c_M ||w - z||`
and `||M(w)|| <= 3 c_M max(1, ||w||)`.

**Proposition S.** Let `Z` be irreducible over `Q`, with primitive Chow form
`F_Z`, and put
`C_1 = kappa_0 log(2 sqrt3 c_M) + (N - kappa_0) log(3 sqrt2 c_M)`.
1. If `Z ∩ Y = ∅`, then `kappa_0 a(F_Z) + (N - kappa_0) b(F_Z) + C_1 deg Z >= 0`.
2. If `Z ⊂ Y`, then `kappa_0 a(F_Z) + (N - kappa_0) b(F_Z) + C_Y deg Z >= 0`, with
   `C_Y = kappa_0 max(0, log(sqrt3 / delta_Y))` and
   `delta_Y = min over y in Ybar ⊂ P^2 of ||y~ x theta~|| / ||y~||`. This is
   positive because `theta~ notin Ybar`.

*Proof.*
1. Proposition C, then (UB2) at each `sigma_j zeta`, then the two displayed
   estimates with `c = c_Z`. The `log|c_Z|` terms cancel against
   `N h_fin = N log|c_Z|`.
2. By (M3), `a(F_Z) >= log|c_Z| + sum_j log(delta_Y ||zeta~_j|| / sqrt3)` and
   `b(F_Z) <= log|c_Z| + sum_j log ||zeta~_j||`. So
   `a >= b - D log(sqrt3/delta_Y)`, and `b >= 0` by (M2). ∎

**Corollary 6 (the target).** Put `C_2 = max(C_1, C_Y)`. Let `F in Z[u]` be a
nonzero product of linear forms `u . (1, zeta)` times a constant. Then

```text
kappa_0 a(F) + (N - kappa_0) b(F) + C_2 deg F  >=  0.                                (CYC)
```

*Proof.* Over `Q`, `F = ± cont(F) prod_i F_(Z_i)^(m_i)`, with `F_(Z_i)` the
primitive Chow forms of irreducible cycles `Z_i`. Each `Z_i` lies in `Y` or is
disjoint from it. By (M1), `a`, `b` and `deg` are additive, and `cont(F)` adds
`N log cont(F) >= 0`. Every summand is nonnegative by Proposition S. ∎

So the exceptional point `z` is ruled out once some such `F` violates (CYC).
Part 3 builds one.
