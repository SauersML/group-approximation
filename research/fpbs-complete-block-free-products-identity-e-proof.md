---
rg: 2
id: fpbs-complete-block-free-products-identity-e-proof
kind: route
title: Match the two-point function to the Green function of a factor-weighted walk, push the resolvent to the quotient, and rule out a flat spectral level set by invariance of domain and homogeneity
target: fpbs-complete-block-free-products-satisfy-identity-e
requires:
  - fpbs-quotient-l2-threshold-sandwich
artifacts:
  - experiments/fpbs-complete-block-green-2026-09-17/check_green_representation.py
  - experiments/fpbs-complete-block-green-2026-09-17/output.txt
---

Complete written proof. Notation as in the target. All kernels are
nonnegative unless complex weights are said explicitly, so sums and
convolutions are rearranged freely in `[0,infinity]`. For a kernel `f >= 0` on
a group `H`, `||f||_H` is the norm of `g -> f * g` on `l2(H)` (possibly
infinite), as in `fpbs-quotient-l2-threshold-sandwich`.

**Imports.**
- (K1) Kesten. Let `nu` be a symmetric finitely supported kernel `>= 0` on a
  countable group `H` whose support generates `H`. Then
  `||lambda_H(nu)|| = ||nu||_1` iff `H` is amenable.
- (K2) Kesten. Let `N ◁ Gamma` and `nu` as in (K1) on `Gamma`. Then
  `||lambda_Gamma(nu)|| = ||lambda_(Gamma/N)(pi_* nu)||` iff `N` is amenable.
  In general `<=` holds.
  Source: Kesten, *Symmetric random walks on groups*, Trans. AMS 92 (1959);
  Woess, *Random walks on infinite graphs and groups*, Ch. 12. Both are
  stated for probability measures and scale to kernels.
- (S) For symmetric `nu >= 0` on `H`,
  `||lambda_H(nu)|| = lim_n (nu^(*2n)(e))^(1/2n)`, since the trace on the
  group von Neumann algebra is faithful. Also
  `||lambda_H(nu)|| = sup{<eta, nu * eta> : eta >= 0, ||eta||_2 = 1}`, which is
  the top of the spectrum.
- (BD) Brouwer's invariance of domain: a continuous injective map from an open
  subset of `R^m` to `R^m` has open image.
- `fpbs-quotient-l2-threshold-sandwich` (ESTABLISHED), part 4:
  `p^Q_(2->2)(N;G) <= p_c(N;G)`.

## Step 0. Multiplicative kernels on the block tree

Every `x in Gamma` has a unique normal form `x = h_1 ... h_L`, with
consecutive letters in different factors and `h_j != e`. For `t in [0,1)^m`
put

```text
kappa_t(x) = prod_j t_(i(j))^(l(h_j)),     l(h) = 1 for finite factors,  l(a^k) = |k| for Z factors.
```

`kappa_t` is symmetric, coordinatewise nondecreasing in `t`, and `kappa_t(e) = 1`.

*Fact 0.* `tau_p(e,x) = kappa_(t(p))(x)`, where `t(p) = (t_1(p),...,t_m(p))`.
The Cayley graph is a block graph. Its blocks are the cosets `gA_i`, which
span `K_(n_i)` or a line, and each prefix `h_1...h_j` is a cut vertex
separating `e` from `x`.
- An open path from `e` to `x` passes every prefix.
- Between consecutive prefixes, the only route is through the block
  containing both, because any excursion out of that block must return
  through the same cut vertex.
- The events for different blocks depend on disjoint edge sets, so they are
  independent.
- Inside a line block, `a^k` is reached through the cut vertices
  `a, ..., a^(k-1)`, which gives the factor `p^|k|`.

This is the same factorization as step 1 of
`fpbs-free-product-block-tree-spectral-proof`. Each `t_i(p)` is strictly
increasing in `p`: the direct edge is pivotal with positive probability.

*Fact 0'.* `||kappa_t||_1 = 1/(1 - Phi(t))` if `Phi(t) < 1`, and `infinity`
otherwise. Here `Phi(t) = sum_i u_i/(1+u_i)`, with `u_i = (n_i - 1) t_i`
(complete block) or `u_i = 2t_i/(1-t_i)` (line). This is the standard
generating function of reduced words. Hence
`p_c(G) = min{p : Phi(t(p)) = 1}`.

## Step 1. The local identity (Lemma 1)

For `t in [0,1)^m` let `beta_i, B, c(t), w_i(t)` be as in the target, with
`t_i` in place of `t_i(p)`. Put `mu_t = sum_i w_i(t) 1_(A_i\{e})`.
- Each `beta_i < 1`: for `K_n`, `(n-1)t^2 < 1 + (n-2)t` iff
  `(t-1)((n-1)t+1) < 0`; for the line, `2t^2 < 1 + t^2`.
- So `w_i(t) > 0` for `t in (0,1)^m`, `c(t) in (0,1]`, and `W: t -> w(t)` is
  real-analytic on a neighbourhood of `[0,1)^m`.

**Lemma 1.** For every `t in [0,1)^m`,
`(delta_e - mu_t) * kappa_t = c(t) delta_e`, where
`(mu * f)(x) = sum_y mu(y) f(y^(-1) x)`. By the symmetry of `mu_t` and
`kappa_t`, also `kappa_t * (delta_e - mu_t) = c(t) delta_e`.

*Proof.*
- Write `E_i = sum_(j != i) u'_j` with `u'_j = (n_j - 1) w_j t_j` (block) or
  `2 w_j t_j` (line), and `S = sum_j u'_j`.
- **At `x != e`**, with first letter `h_1 in A_i`, the terms `y^(-1) x` for
  `y in S` are as follows.
  - Complete block `A_i`, `y in A_i`:
    - `y = h_1` deletes the letter, giving `kappa_t(x)/t_i`;
    - the `n_i - 2` other `y` replace `h_1`, giving `kappa_t(x)`.
  - Line `A_i`, `h_1 = a^k`: one of `y = a^(±1)` shortens `|k|` (factor
    `1/t_i`) and the other lengthens it (factor `t_i`).
  - `y in A_j`, `j != i`: the letter is prepended, giving `t_j kappa_t(x)`,
    `n_j - 1` times (twice for a line).
- So the identity at `x` reads
  `1 - w_i/t_i - (n_i - 2) w_i - E_i = 0` (block) or
  `1 - w_i/t_i - w_i t_i - E_i = 0` (line). Equivalently
  `w_i = t_i (1 - E_i)/D_i`.
- Multiply by `(n_i - 1) t_i` (resp. `2 t_i`). The equations become
  `u'_i = beta_i (1 - S + u'_i)`, that is,
  `u'_i = (beta_i/(1-beta_i)) (1 - S)`.
- Summing over `i` gives `S = B(1-S)`, so `1 - S = 1/(1+B) = c`. Substituting
  back gives exactly the stated `w_i`. So the identity holds at every
  `x != e`.
- **At `x = e`**: `kappa_t(e) - sum_y mu_t(y) kappa_t(y^(-1)) = 1 - S = c`. ∎

The artifact script checks Lemma 1 on balls of radius 6, to `2e-16`, for five
block configurations and four values of `p`.

*One-type check.* For `F_d` (all `d` blocks lines, `t = p`),
`w = p/(1 + (2d-1)p^2)` and `c = (1-p^2)/(1+(2d-1)p^2)`. These are `z(p)` and
`phi(p)` of `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`.

*The `l1` relation.* Summing Lemma 1 over `x` when `Phi(t) < 1` gives
`||kappa_t||_1 (1 - ||mu_t||_1) = c(t)`. Both sides of
`||mu_t||_1 = 1 - c(t)(1 - Phi(t))` are rational in `t` and agree on the open
set `{Phi < 1}`, so they agree on `[0,1)^m`. Hence
`||mu_t||_1 < 1` iff `Phi(t) < 1`, and `||mu_t||_1 = 1` iff `Phi(t) = 1`.

## Step 2. The Green representation on Gamma

Write `rho_Gamma(t) = ||lambda_Gamma(mu_t)||` and `f_x(t) = c(t) G_(mu_t)(x) - kappa_t(x)`.

**(2a) The `l1` region.** Let `R_1 = {t in (0,1)^m : Phi(t) < 1}`. On `R_1`,
`||mu_t||_1 < 1`. Iterating Lemma 1 gives
`kappa_t = c sum_(n<M) mu_t^(*n) + mu_t^(*M) * kappa_t`, and the remainder has
`l1` norm `||mu_t||_1^M ||kappa_t||_1 -> 0`. So `f_x = 0` on `R_1`. `R_1` is
open, and it is connected, since it is a down-set in the open orthant that
contains a small cube at `0`.

**(2b) Analyticity.** Let `Omega = {t in (0,1)^m : rho_Gamma(t) < 1}`. It is open,
because `t -> mu_t` is continuous into `l1` and `||lambda(mu)|| <= ||mu||_1`.
Fix `t_0 in Omega` and `eps > 0` with `(1+eps) rho_Gamma(t_0) < 1`.
- For complex weights with `|w_i| <= (1+eps) w_i(t_0)`, `|mu_w^(*n)(x)|` is at
  most `mu_((1+eps)w(t_0))^(*n)(x)`, which is at most
  `<delta_x, lambda(mu_((1+eps)w(t_0)))^n delta_e>`, and this is at most
  `((1+eps) rho_Gamma(t_0))^n`.
- So `w -> G_(mu_w)(x)` is a uniformly convergent series of polynomials on a
  complex polydisc containing `w(t_0)`, and it is holomorphic there.
- Composing with the real-analytic `W` shows that `f_x` is real-analytic on
  `Omega`.
- `R_1 ⊂ Omega`, by (2a) and `rho <= ||.||_1`. Let `Omega_0` be the connected
  component of `Omega` that contains `R_1`.
- A real-analytic function that vanishes on a nonempty open subset of a
  connected open set vanishes identically.

So `kappa_t = c(t) G_(mu_t)` on `Omega_0`. **(2.1)**

**(2c) Injectivity of `W` on `Omega_0`.** By (2.1),
`t_i = kappa_t(a_i) = G_(mu_t)(a_i)/G_(mu_t)(e)` for any `a_i in A_i\{e}`, since
`kappa_t(e) = 1`. So `t` is a function of `w(t)`, and `W` is injective on
`Omega_0`. **(2.2)**

**(2d) Up to `p_(2->2)(G)`.** Let `p < p_(2->2)(G)` and `p' <= p`. Then
`||kappa_(t(p'))||_Gamma <= ||kappa_(t(p))||_Gamma < infinity`, by
monotonicity of nonnegative kernels.
- Lemma 1 on both sides gives
  `(1 - lambda(mu)) lambda(kappa) = lambda(kappa) (1 - lambda(mu)) = c`, as
  bounded operators. So `1 - lambda(mu_(t(p')))` is invertible.
- By (S), `||lambda(mu)||` lies in the spectrum. Hence
  `rho_Gamma(t(p')) != 1`.
- `p' -> rho_Gamma(t(p'))` is continuous, vanishes at `p' = 0`, and never
  equals 1 on `[0,p]`. Hence `rho_Gamma(t(p)) < 1`.
- The curve `t([0,p])` lies in `Omega`. It meets `R_1` near `p' = 0`, so it
  lies in `Omega_0`.

This proves Theorem A.1. The converse also holds. On
`t((0,1)) ∩ Omega_0`, (2.1) makes `lambda(kappa) = c sum lambda(mu)^n`
bounded. So `p_(2->2)(G) = sup{p : t([0,p]) ⊂ Omega_0}`.

## Step 3. Pushforward to the quotient

`pi_*` is a homomorphism of `l1` algebras, and on nonnegative series it
commutes with summation (Tonelli). Put `mu-bar_t = pi_* mu_t` and
`r_Q(t) = ||lambda_Q(mu-bar_t)||`. On `Omega_0`, (2.1) gives

```text
sigma_t := pi_* kappa_t = c(t) G_(mu-bar_t)     on Q.        (3.1)
```

For `t = t(p)`, `sigma_t = sigma^N_p` and `sigma_t(e) = chi^N_p`.

**Lemma 3.** For `t in Omega_0`:
- (a) `||sigma_t||_Q < infinity` iff `r_Q(t) < 1`.
- (b) If `r_Q(t) < 1` then `sigma_t(e) < infinity`, and if `sigma_t(e) < infinity`
  then `r_Q(t) <= 1`.

*Proof.* (a) If `r = r_Q(t) < 1`, the Neumann series converges in norm. Now let
`r >= 1` and `eps > 0`.
- By (S) choose `eta >= 0`, finitely supported, `||eta||_2 = 1`, with
  `<eta, mu-bar * eta> >= 1 - eps`.
- Let `m_eta` be its spectral measure for the self-adjoint `lambda_Q(mu-bar)`.
  By Jensen, `<eta, mu-bar^(*2k) * eta> = ∫ x^(2k) dm_eta >= (1-eps)^(2k)`.
- The odd terms are `>= 0`, since `eta` and the kernel are nonnegative.
- So `<eta, G_(mu-bar) * eta> >= sum_k (1-eps)^(2k) >= 1/(2 eps)`. Since
  `eps` is arbitrary, `||sigma_t||_Q = infinity`.

(b) The first half is the Neumann series. For the second, `G_(mu-bar)(e) < infinity`
forces `limsup (mu-bar^(*2n)(e))^(1/2n) <= 1`, which is `r_Q <= 1` by (S). ∎

Also `r_Q(t) >= rho_Gamma(t)`: `mu-bar^(*n)(e) = mu^(*n)(N) >= mu^(*n)(e)`,
then apply (S). Both `r_Q` and `rho_Gamma` are continuous on `[0,1)^m` and
positively homogeneous of degree 1 in the weights:
`||lambda(s nu)|| = s ||lambda(nu)||`.

## Step 4. Claim E

**Lemma 4 (infinite normal subgroups are nonamenable).** Let `Gamma` be as in
the target, and `N ◁ Gamma` infinite. Then `N` is nonamenable.

*Proof.* By the Kurosh subgroup theorem, `N` is a free product of a free group
and of subgroups `N ∩ g A_i g^(-1)`. A free product of nontrivial groups is
amenable only if it has one factor or is `Z/2 * Z/2`. So an amenable `N` is
one of the following.
- **`N` lies in a conjugate `g A_i g^(-1)`.** For every `h`, normality gives
  `N ⊂ g A_i g^(-1) ∩ h g A_i g^(-1) h^(-1)`. Choose `h` with `h g A_i != g A_i`.
  In the block tree (element vertices and coset vertices), the stabilizers of
  two distinct coset vertices meet inside the stabilizer of every element
  vertex on the path between them. Element-vertex stabilizers are trivial.
  So `N = 1`.
- **`N` is infinite cyclic or infinite dihedral.** Then `N` has a
  characteristic infinite cyclic subgroup `<z>`, so the centralizer `C(z)` has
  index at most 2 in `Gamma`. In a free product, the centralizer of an element
  of infinite order is infinite cyclic. It lies in a conjugate of a `Z` factor
  if `z` is conjugate into one, and otherwise it is cyclic by the standard
  centralizer theorem (Magnus–Karrass–Solitar, §4.1). Then `Gamma` is
  virtually `Z`. That is impossible, since `Gamma` contains `F_2`, by the same
  Kurosh count applied to the kernel of `Gamma -> prod A_i^(ab)`, or directly
  by ping-pong.
∎

Let `N ◁ Gamma` be infinite. Write `r_Q(p) = r_Q(t(p))` and
`rho_Gamma(p) = rho_Gamma(t(p))`. Let `p_Q = sup{ p : r_Q < 1 on [0,p] }`.
- `r_Q` is continuous with `r_Q(0) = 0`, so `p_Q > 0`.
- For `p < p_Q`, `rho_Gamma <= r_Q < 1` on `[0,p]`. The curve `t([0,p])` lies
  in `Omega`, meets `R_1`, and so lies in `Omega_0`. By (2.1) and the Neumann
  series, `||tau_p||_Gamma < infinity`.
- Hence `p_Q <= p_(2->2)(G)`. Also `p_(2->2)(G) < 1`: by Fact 0' applied to
  `t^2`, `sum_x tau_p(e,x)^2` diverges for `p` near 1.
- By continuity, `r_Q(p_Q) = 1`, and `p_Q = min{p : r_Q(p) = 1}`.

**(4a) `t(p_Q) ∈ Omega_0` and `p_Q < p_(2->2)(G)`.**
- By (K2) and Lemma 4, `rho_Gamma(p_Q) < r_Q(p_Q) = 1`. Here the support
  `∪ (A_i\{e})` generates `Gamma` and every `w_i > 0`.
- So `t(p_Q) ∈ Omega`. It is a limit of curve points of `Omega_0`, and
  `Omega` is open, so it lies in `Omega_0`.
- Fix an open ball `U` about `t(p_Q)` with `U ⊂ Omega_0`.
- For `p` slightly above `p_Q`, `t([0,p]) ⊂ Omega_0`. So, by the converse in
  (2d), `p_(2->2)(G) > p_Q`.

**(4b) `p^Q_(2->2)(N;G) = p_Q`.**
- For `p < p_Q`, Lemma 3(a) gives `||sigma^N_p||_Q < infinity`.
- At `p_Q`, (3.1) holds and `r_Q = 1`, so Lemma 3(a) gives
  `||sigma^N_(p_Q)||_Q = infinity`.
- `||sigma^N_p||_Q` is nondecreasing in `p`.

**(4c) `chi^N_p = infinity` for every `p > p_Q`.** Suppose not. By
monotonicity in `p`, there is `p_2 > p_Q` with `chi^N_(p_2) < infinity` and
`t(p_2)` as close to `t(p_Q)` as we like.
- Let `P = {t : t(p_Q) <= t <= t(p_2)}` (coordinatewise). Its interior `P°`
  is nonempty, because every `t_i` is strictly increasing. For `p_2` close to
  `p_Q`, `P ⊂ U ⊂ Omega_0`, so (3.1) holds on `P`.
- For `t in P`, monotonicity of `kappa_t` in `t` gives two bounds:
  - `sigma_t(e) <= sigma_(t(p_2))(e) = chi^N_(p_2) < infinity`, so
    `r_Q(t) <= 1` by Lemma 3(b);
  - `||sigma_t||_Q >= ||sigma_(t(p_Q))||_Q = infinity`, so `r_Q(t) >= 1` by
    Lemma 3(a).
- So `r_Q ≡ 1` on `P`.
- By (2.2) and (BD), `O = W(P°)` is a nonempty open subset of the weight space
  `(0,infinity)^m`, on which `w -> ||lambda_Q(pi_* sum_i w_i 1_(A_i\{e}))||`
  is identically 1.
- Take `w in O` and `s != 1` near 1 with `s w in O`. Homogeneity gives the
  value `s`, a contradiction.

So `p_c(N;G) <= p_Q`. Part 4 of the sandwich gives
`p_c(N;G) >= p^Q_(2->2)(N;G) = p_Q`. Hence

```text
p_c(N;G) = p^Q_(2->2)(N;G) = p_Q < p_(2->2)(G).
```

This is Theorem A.3. Theorem A.2 is (3.1) on `t([0,p_Q]) ⊂ Omega_0`, and
Theorem A.1 is (2d). ∎

## Step 5. The Kesten criterion and the C1 type

By Fact 0' and the `l1` relation, `||mu_(t(p))||_1 < 1` for `p < p_c(G)`, and
`||mu_(t(p_c(G)))||_1 = 1`. Also `||mu-bar||_1 = ||mu||_1`, and the support of
`mu-bar` generates `Q`.
- **`Q` nonamenable.** By (K1), `r_Q(p_c(G)) < 1`. On `[0,p_c(G))`,
  `r_Q <= ||mu||_1 < 1`. So `p_Q > p_c(G)`, and by (4b)
  `||sigma^N_(p_c(G))||_Q < infinity`. This is type (i).
- **`Q` amenable.** By (K1), `r_Q(p) = ||mu_(t(p))||_1`, which is `< 1` exactly
  for `p < p_c(G)`. So `p_c(N;G) = p_Q = p_c(G)`. This is type (iii), and it
  agrees with `fpbs-co-amenable-subgroup-relative-threshold-is-pc`.
- **Type (ii)** needs `p^Q_(2->2) < p_c(N;G)`, which Step 4 rules out.

This proves Theorem A.4. For A.5: (3.1) holds at `t(p_Q)`, so
`chi^N_(p_Q) = c G_(mu-bar)(e)` with `r_Q = 1`. This is finite iff `mu-bar` is
rho-transient. ∎

## Step 6. Theorem B, and where the method stops

Steps 3 and 4 use only the following:
- the local identity on an `m`-parameter family `kappa_t`, monotone in `t`,
  that contains the percolation curve with strictly increasing coordinates;
- `c > 0`;
- the representation (2.1) together with injectivity of `W`;
- (K2) at a single point, which needs `N` nonamenable;
- homogeneity of the spectral radius.

This is Theorem B of the target. On the complete-block class, the cut vertices
of the block tree supply every item.

For a block `Cay(A_i,S_i)` that is not complete, the method needs the block
two-point function `g -> tau^(A_i)_p(e,g)` to be a first-passage function of
a symmetric block walk with uniform loop weight. This was not examined here.
Where it fails, `tau_p` is not the Green function of a walk with factor
weights, and Step 1 has no analogue.
