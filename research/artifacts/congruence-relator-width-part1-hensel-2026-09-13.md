# Congruence relator width, part 1: Singer pairs, the Hensel lemma, and the non-near-scalar cases

Lane `ex2-weak-sofic-affine-targets`, 2026-09-13. Unreviewed. Target claim:
`simple-group-width-over-congruence-targets`. Part 2 treats near-scalar residue tuples.

## 0. Setting

- `R` is a **finite chain ring**: a finite local ring whose maximal ideal `m = pi R` is principal, with
  residue field `F_q`, `m^k = 0` and `m^(k-1) != 0`. Examples: `F_q[t]/(t^k)`, `Z/p^k`, `O_K/p^k`.
- `Q = SL_n(R)`, with reduction `g -> gbar in SL_n(q)`. Every element of `SL_n(q)` is a product of
  elementary matrices, and these lift entrywise, so reduction is onto.
- `K_j = ker(SL_n(R) -> SL_n(R/m^j))` for `1 <= j <= k`, so `K_k = 1`. `K_1` has `p`-power order.
- **Teichmueller scalars.** `R^x = T x (1 + m)` with `T ≅ F_q^x`, since `|1 + m|` is a power of `p`.
  The section `mu -> mu~` is multiplicative, so `mu^n = 1` gives `mu~^n = 1`. `Z_T = {mu~ · 1 : mu^n = 1}`
  is central in `Q` and maps onto `Z(SL_n(q))`.
- `[x, y] = x y x^-1 y^-1`. `Cons_K(S)` is the set of products of at most `K` `Q`-conjugates of elements
  of `S^(+-1)`. For `u, v in Z_T · Cons_m(S)`, `[u, v] in Cons_(2m)(S)`, because central factors cancel
  and `[p, v] = p · (v p^-1 v^-1)`.

## 1. Layers

**Lemma 1.1.** For `1 <= j <= k - 1` the map `theta_j : K_j -> sl_n(F_q)`, `1 + pi^j Y -> Ybar`, is a
well-defined surjective homomorphism with kernel `K_(j+1)`. For `g in Q` and `gamma in K_j`,
```text
theta_j(g gamma g^-1) = Ad_(gbar) theta_j(gamma),     theta_j([g, gamma]) = (Ad_(gbar) - 1) theta_j(gamma).
```
In particular `K_1` acts trivially on `K_j/K_(j+1)`, and that layer is central in `K_1/K_(j+1)`.

*Proof.*
- *Well defined.* In a chain ring, `pi^j y in m^(j+1)` iff `y in m`, because `j + 1 <= k`.
- *Homomorphism.* `(1 + pi^j Y)(1 + pi^j Y') = 1 + pi^j (Y + Y') + pi^(2j) Y Y'`, and `2j >= j + 1`.
- *Trace zero.* `det(1 + pi^j Y) ≡ 1 + pi^j tr Y` modulo `m^(j+1)`, since products of two off-identity
  entries lie in `m^(2j)`. So `det = 1` forces `tr Ybar = 0`.
- *Onto.* `1 + pi^j c~ E_ab` (`a != b`) and the diagonal matrix with `1 + pi^j c~` at `a` and its inverse at
  `b` lie in `K_j` and map to `c E_ab` and `c (E_aa - E_bb)`. These span `sl_n(F_q)`.
- *Conjugation.* `g (1 + pi^j Y) g^-1 = 1 + pi^j g Y g^-1`. Then `[g, gamma] = (g gamma g^-1) gamma^-1`
  has image `Ad_(gbar) Ybar - Ybar`.

## 2. Singer pairs

**Lemma 2.1.** Let `n >= 3`, or `n = 2` and `q >= 3`. There are `sigma_1, sigma_2 in SL_n(q)` of order
prime to `p` with `C(sigma_1) ∩ C(sigma_2) = F_q · 1`, where `C` is the centralizer in `M_n(F_q)`.

*Proof.*
- **The torus.** Identify `F_q^n` with `F_(q^n)`, let `zeta` generate `F_(q^n)^x`, and let `sigma` be
  multiplication by `zeta^(q-1)`.
  - `det sigma = N(zeta)^(q-1) = 1`, and its order `(q^n - 1)/(q - 1)` is prime to `p`.
  - `F_q(zeta^(q-1)) = F_(q^n)`: otherwise `(q^n - 1) | (q - 1)(q^d - 1)` for some `d <= n - 1`, but
    `(q - 1)(q^(n-1) - 1) < q^n - 1`.
  - So `A := C(sigma)` is the commutant of `F_(q^n)`, which is `End_(F_(q^n))(F_(q^n)) = F_(q^n)`.
- **Reduction to a normalizer condition.** For `s in SL_n(q)`, `C(s sigma s^-1) = s A s^-1`.
  - `A ∩ s A s^-1` is a subalgebra of the field `A`, so it is a subfield `F_(q^d)`.
  - Suppose `d > 1`, and pick a prime `l | d`. `A` has a unique subfield `B` of order `q^l`, and
    `B <= s A s^-1`. The unique subfield of that order in `s A s^-1` is `s B s^-1`, so `s B s^-1 = B`.
  - So any `s` normalizing no subfield `B <= A` of prime degree `l >= 2` gives `A ∩ s A s^-1 = F_q`.
- **`n >= 3`: a transvection works.** Let `s = 1 + v phi` with `phi(v) = 0`, and suppose `s B s^-1 = B`.
  - Conjugation by `s` is a field automorphism `tau` of `B` over `F_q`, so `s(beta x) = beta^tau s(x)`.
  - `H = ker phi` has codimension `1`. For `beta in B^x`, `H ∩ beta^-1 H` has codimension `<= 2 < n`, so it
    contains some `x != 0`. Then `beta x = s(beta x) = beta^tau x`, so `beta = beta^tau`.
  - So `tau = 1`, and `s` is `B`-linear. Then `im(s - 1)` is a `B`-subspace, of `F_q`-dimension a
    multiple of `l >= 2`. That contradicts `rk(s - 1) = 1`.
- **`n = 2`, `q >= 3`: counting.** Here `B = A`. Its normalizer in `GL_2(q)` is `A^x x| <Frobenius>`.
  At most `q + 1` of its `A`-linear elements and at most `q + 1` of its semilinear elements have
  determinant `1`. Since `|SL_2(q)| = q(q^2 - 1) > 2(q + 1)`, some `s in SL_2(q)` does not normalize `A`.
- Put `sigma_1 = sigma` and `sigma_2 = s sigma s^-1`.

**Lemma 2.2 (layer surjectivity).** For `sigma_1, sigma_2` as in Lemma 2.1, the map
```text
Lambda : sl_n(F_q)^2 -> sl_n(F_q),   (Y_1, Y_2) -> (Ad_(sigma_1) - 1) Y_1 + (Ad_(sigma_2) - 1) Y_2
```
is onto.

*Proof.* Use the nondegenerate trace form `<Z, Y> = tr(Z Y)` on `M_n(F_q)`, for which
`sl_n^perp = F_q · 1`.
- Let `Z` be orthogonal to `im Lambda`. For `Y in sl_n`, `tr((sigma_i^-1 Z sigma_i - Z) Y) = 0`, so
  `sigma_i^-1 Z sigma_i = Z + c_i · 1`.
- Iterating `o` times, with `o` the order of `sigma_i`, gives `o c_i = 0`. Since `p` does not divide `o`,
  `c_i = 0`, so `Z in C(sigma_1) ∩ C(sigma_2) = F_q · 1`.
- So `dim im Lambda >= n^2 - 1`. Also `im Lambda <= sl_n`, since `Ad Y - Y` has trace `0`.

## 3. The Hensel lemma

**Lemma 3.1.** Let `n, q` be as in Lemma 2.1, and `g_1, g_2 in SL_n(R)` with `gbar_i = sigma_i`. Every
`kappa in K_1` equals `[g_1, beta_1][g_2, beta_2]` for some `beta_1, beta_2 in K_1`.

*Proof.* By induction on `j = 1, ..., k`, find `beta_1, beta_2 in K_1` with
`eps_j := ([g_1, beta_1][g_2, beta_2])^-1 kappa in K_j`. For `j = 1`, take `beta_i = 1`. Suppose it holds for
some `j <= k - 1`.
- By Lemma 2.2, choose `Y_1, Y_2 in sl_n(F_q)` with `Lambda(Y_1, Y_2) = theta_j(eps_j)`. By Lemma 1.1,
  choose `gamma_i in K_j` with `theta_j(gamma_i) = Y_i`.
- `[g_i, beta_i gamma_i] = [g_i, beta_i] · beta_i [g_i, gamma_i] beta_i^-1`. The second factor lies in `K_j`,
  and by Lemma 1.1 its image under `theta_j` is `(Ad_(sigma_i) - 1) Y_i`.
- The layer `K_j/K_(j+1)` is central in `K_1/K_(j+1)`, and `[g_i, beta_i] in K_1`. So modulo `K_(j+1)`,
  ```text
  [g_1, beta_1 gamma_1][g_2, beta_2 gamma_2] ≡ [g_1, beta_1][g_2, beta_2] · x_1 x_2 ,   theta_j(x_1 x_2) = theta_j(eps_j) .
  ```
- So the new error lies in `K_(j+1)`. At `j = k` the error is `1`.

**Corollary 3.2.** Let `S <= Q` be a normal subset. If `g_i = z_i P_i` with `z_i in Z_T`,
`P_i in Cons_m(S)` and `gbar_i = sigma_i`, then `K_1 <= Cons_(4m)(S)`.

*Proof.* `[z_i P_i, beta] = [P_i, beta] = P_i · (beta P_i^-1 beta^-1) in Cons_(2m)(S)`. Apply Lemma 3.1.

## 4. Covering from a residue class

**Proposition 4.1.** Let `n, q` be as in Lemma 2.1, and `h in SL_n(R)`. Suppose the class `Sbar` of the
image of `hbar` in `PSL_n(q)` satisfies `Sbar^(k_0) = PSL_n(q)`. Then `SL_n(R) = Z_T · Cons_(5 k_0)(h)`.

*Proof.*
- **Residues.** Every `gbar in SL_n(q)` equals `zbar · prod_(i <= k_0) sbar_i hbar sbar_i^-1` with `zbar`
  central. Lift the `sbar_i` to `s_i in Q`, and put `P = prod_i s_i h s_i^-1 in Cons_(k_0)(h)`. With
  `zbar = mu · 1`, `mu~ P` reduces to `gbar`. So `SL_n(R) = Z_T · Cons_(k_0)(h) · K_1`.
- **Kernel.** Applied to `sigma_1, sigma_2`, this gives `g_i = z_i P_i` as in Corollary 3.2 with `m = k_0`.
  So `K_1 <= Cons_(4 k_0)(h)`.

Nothing depends on `k` or on `R` beyond its residue field.

## 5. Relator width: the scalar, bounded-rank and proportional cases

Let `G = <X | R>` be an infinite finitely presented simple group, with the template (T) of
`simple-group-psl-width-is-finite-field-linear-soficity-proof`, Section 1: words `u_(x,j), v_(x,j)` of length
`<= L` and `J, J'`. It suffices to put every template commutator `[u(a), v(a)]` in a bounded `Cons`. Let
`a in SL_n(R)^X`, `abar` its reduction, and `P = max_x rho(abar_x)`, where `rho(g) = min_lambda rk(g - lambda)`.
A tuple in `SL_n(R)/Z_0` lifts to `SL_n(R)`, so quotients by central subgroups are covered too.

- **Case S: `P = 0`.** Every `abar_x = mu_x · 1`, so `a_x in Z_T · K_1`. That subgroup is nilpotent,
  since `Z_T` is central and `K_1` is a `p`-group. By item 1 of
  `perfect-group-relator-width-over-nilpotent-groups`, `a_x in Cons_(K(x))(R(a))`.
- **Case B: `n < D`, `P >= 1`.** No hypothesis on `G` beyond simplicity is used.
  - Some relator value has non-central residue. Otherwise, by (E1) in `PSL_n(q)`, every `abar_x` is
    central and `P = 0`.
  - *Large fields.* For `q >= q_1(D)` (take `q_1 >= 3`), Section 3 of the PSL proof gives
    `Sbar^(2cD^2) = PSL_n(q)`. By Proposition 4.1, `[u(a), v(a)] in Cons_(20 c D^2)(R(a))`.
  - *Small fields.* The groups `SL_n(q)` with `n < D` and `q < q_1(D)` are finitely many. `K_1` is
    nilpotent, so `relator-width-over-nilpotent-by-locally-finite-groups`, with the variety generated
    by those groups, bounds `w` by a constant `K(G, D)`, uniformly in `R`.
- **Case P: `n >= D`, `P >= n/(c_5 |X|)`** (`c_5` is fixed in part 2, Section 1). Assume `G` is not linear
  sofic over finite fields.
  - *A relator far from the scalars.* Item 0 of `simple-group-psl-width-is-finite-field-linear-soficity`
    gives `r*` with `rho(r*(abar)) >= (delta_0/2) min(P, n/2) >= eta' n`, where `eta' = delta_0/(2 c_5 |X|)`.
  - *Covering the residue group.* By (2.1) of the PSL proof, for `D^2 eta' >= 8`,
    `log|Sbar| >= (eta'/2) n^2 log q`. Liebeck--Shalev gives `Sbar^(k_1) = PSL_n(q)` with
    `k_1 = ceil(2c/eta')`.
  - *Conclusion.* Proposition 4.1 with `h = r*(a)` gives `SL_n(R) = Z_T · Cons_(5 k_1)(R(a))`, so
    `[u(a), v(a)] in Cons_(10 k_1)(R(a))`.

In each case the bound is independent of `n`, `q`, `k` and `R`. The remaining case,
`n >= D` with `1 <= P < n/(c_5|X|)`, is part 2.
