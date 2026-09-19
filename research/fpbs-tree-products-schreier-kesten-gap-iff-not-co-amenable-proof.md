---
rg: 2
id: fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable-proof
kind: route
title: Nonbacktracking polynomials bound every coset of a non-co-amenable tree section uniformly, and co-amenability of products of sections reduces every non-co-amenable subgroup of a tree product to one tilted coordinate
target: fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable
requires:
  - fpbs-tree-product-thin-section-subgroups-have-tilt-gap
  - fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap
  - fpbs-co-amenable-subgroup-relative-threshold-is-pc
artifacts:
  - experiments/fpbs-coset-sections-2026-09-17/check_coset_sections.py
  - experiments/fpbs-coset-sections-2026-09-17/output.txt
---

Complete written proof. Notation is as in the target. All groups are
finitely generated. Right cosets are written `Jx`, and `Gamma` acts on
`J\Gamma` on the right. A subgroup `J <= Gamma` is **co-amenable** if there
is a mean `m` on `ℓ^∞(J\Gamma)` with `m(f^g) = m(f)` for all `g`, where
`f^g(Jx) = f(Jxg)`.

## Step 0. Four facts about co-amenability

**F1 (upward).** If `A <= B <= Gamma` and `A` is co-amenable in `Gamma`, then
so is `B`.

*Proof.* The map `pi: A\Gamma -> B\Gamma`, `Ax -> Bx`, is well defined and
commutes with the right action. Set `m_B(f) = m_A(f ∘ pi)`. This is a mean,
and `(f ∘ pi)^g = f^g ∘ pi`, so it is invariant.

**F2 (products).** If `J_i` is co-amenable in `Gamma_i` for `i = 1, 2`, then
`J_1 x J_2` is co-amenable in `Gamma_1 x Gamma_2`. By induction, the same
holds for finitely many factors.

*Proof.* `(J_1 x J_2)\(Gamma_1 x Gamma_2) = J_1\Gamma_1 x J_2\Gamma_2`,
equivariantly. For bounded `f` on it, put
`m(f) = m_1( u -> m_2( v -> f(u,v) ) )`. The inner function is bounded, so
`m` is a mean. Right translation by `(g_1,1)` translates the outer argument,
and `m_1` is invariant. Right translation by `(1,g_2)` translates the inner
argument, and `m_2` is invariant. These elements generate the product, so
`m` is invariant.

**F3.** If `A` is amenable, `{1}` is co-amenable in `A`. This is the
definition of amenability, since `{1}\A = A`. If `N` is normal in `Gamma`
with `Gamma/N` amenable, then `N` is co-amenable, since `N\Gamma = Gamma/N`
with the right regular action.

**F4 (transitivity).** If `K <= L <= Gamma`, with `K` co-amenable in `L` and
`L` co-amenable in `Gamma`, then `K` is co-amenable in `Gamma`.

*Proof.* Let `n` be an `L`-invariant mean on `ℓ^∞(K\L)` and `m` a
`Gamma`-invariant mean on `ℓ^∞(L\Gamma)`. For bounded `f` on `K\Gamma` and
`g in Gamma`, put `F(Lg) = n( Kl -> f(Klg) )`.
- *Well defined.* Replacing `g` by `l'g` with `l' in L` replaces the
  argument by its right translate by `l'`, and `n` is `L`-invariant.
- *Equivariant.* `F` is bounded by `sup|f|`, and `(f^g)` gives `F^g`.

So `f -> m(F)` is a `Gamma`-invariant mean on `ℓ^∞(K\Gamma)`.

**F5.** If `Lambda` is nonamenable and `J <= Lambda` is co-amenable, then `J`
is infinite.

*Proof.* If `J` is finite, set `M(f) = m( Jx -> (1/|J|) sum_(j in J) f(jx) )`
for bounded `f` on `Lambda`. This is a well-defined invariant mean on
`ℓ^∞(Lambda)`, contradicting nonamenability. The `k`-regular tree with
`k >= 3` has nonamenable `Lambda`.

## Step 1. Nonbacktracking polynomials in the group algebra

Let `T = Cay(Lambda, S_Lambda)` be the `k`-regular tree, `q = k - 1`, and let
`sigma_n = 1_(S_n) in C[Lambda]`. The product is convolution, so
`sigma_n sigma_1 = sum_(y in S_n, s in S_Lambda) delta_(ys)`.

**Claim.**

```text
sigma_1 sigma_1 = sigma_2 + (q+1) sigma_0,
sigma_n sigma_1 = sigma_(n+1) + q sigma_(n-1)     (n >= 2).
```

*Proof.* The pairs `(y,s)` with `|y| = n >= 1` correspond to the directed
edges `y -> ys` of the tree leaving `S_n`. Since `T` is a tree:
- every `z in S_(n+1)` is reached from exactly one `y in S_n`, its neighbour
  toward `1`;
- every `z in S_(n-1)` is reached from each of its neighbours in `S_n`. There
  are `q` of them if `n >= 2`, and `q + 1` if `n = 1` (then `z = 1`).

Only generators of the tree are used, so the claim holds for every `Lambda`
whose Cayley graph is the `k`-regular tree, including the `Z/2` free factors.

**Polynomials.** Define `P_0 = 1`, `P_1 = x`, `P_2 = x^2 - (q+1)` and
`P_(n+1) = x P_n - q P_(n-1)` for `n >= 2`. By induction on `n`,
`sigma_n = P_n(sigma_1)` in `C[Lambda]`.

**Closed form.** Let `t = x/(2 sqrt q)`, let `U_j` be the Chebyshev
polynomials of the second kind, and put `U_(-1) = 0`. For `n >= 1`,

```text
P_n(x) = q^(n/2) [ U_n(t) - q^(-1) U_(n-2)(t) ].
```

*Check.*
- `n = 1`: `sqrt q U_1(t) = sqrt q · 2t = x`.
- `n = 2`: `q(4t^2 - 1) - 1 = x^2 - q - 1`.
- For `n >= 2`, `U_(j+1) = 2t U_j - U_(j-1)` holds for every `j >= 0`. Using it
  at `j = n` and at `j = n - 2 >= 0`,
  `x P_n - q P_(n-1) = q^((n+1)/2) [ U_(n+1) - q^(-1) U_(n-1) ]`.

Artifact part (a) checks the recursion against this closed form numerically.

## Step 2. The Chebyshev bound

For `x >= 0` let `mu_+(x) = (x + sqrt(x^2 - 4q))/2` if `x >= 2 sqrt q`, and
`mu_+(x) = sqrt q` otherwise. Then `mu_+` is continuous and nondecreasing,
strictly increasing on `[2 sqrt q, infinity)`, and
`mu_+(q+1) = ((q+1) + (q-1))/2 = q`.

**Claim.** For every real `x` and every `n >= 0`,

```text
|P_n(x)| <= (1 + 1/q) (n+1) mu_+(|x|)^n .
```

*Proof.* The case `n = 0` is trivial. Let `n >= 1`. Since
`U_j(-t) = (-1)^j U_j(t)`, we may take `x >= 0`.
- *If `t <= 1`.* Then `|U_j(t)| <= j + 1`, so
  `|P_n| <= q^(n/2) (n + 1 + (n-1)/q) <= (1 + 1/q)(n+1) q^(n/2)`.
- *If `t > 1`.* Write `t = cosh theta` with `theta > 0`. Then
  `U_j(t) = sum_(i=0)^j e^((j-2i) theta)`, which lies in
  `(0, (j+1) e^(j theta)]`. So
  `|P_n| <= q^(n/2) [ (n+1) e^(n theta) + (n-1) e^((n-2) theta)/q ]`, which is
  at most `(1 + 1/q)(n+1)(sqrt q e^theta)^n`. Finally
  `sqrt q e^theta = sqrt q (t + sqrt(t^2 - 1)) = mu_+(x)`.

Artifact part (b) checks the bound on a grid, with worst ratio `0.857`.

## Step 3. Lemma A (uniform coset counts)

Let `J <= Lambda`. Let `pi` be the right quasi-regular representation on
`ℓ^2(J\Lambda)`, `(pi(g) f)(Jx) = f(Jxg)`. It is a unitary representation,
since `pi(g) pi(h) = pi(gh)`, and it extends to `C[Lambda]`. Put
`A_n = pi(sigma_n)`.

- `A_1 = (q+1) P`, where `P` is the simple random walk operator of
  `Sch(J\Lambda, S_Lambda)`, counted with multiplicity. Since `S_Lambda` is
  symmetric and `pi(s)^* = pi(s^(-1))`, `A_1` is self-adjoint. So its
  spectrum lies in `[-(q+1) rho_J, (q+1) rho_J]`, where
  `rho_J = ||P|| <= 1`.
- By Step 1, `A_n = P_n(A_1)`. By the spectral theorem and Step 2, with
  `mu_+` nondecreasing,

  ```text
  ||A_n|| <= sup_(|x| <= (q+1) rho_J) |P_n(x)| <= (1 + 1/q)(n+1) r_J^n,     r_J = mu_+((q+1) rho_J).
  ```

- **Counts as matrix entries.** For `z in Lambda`,
  `(A_m delta_(Jz))(J) = sum_(w in S_m) delta_(Jz)(Jw) = #(Jz ∩ S_m)`.
  So `#(Jz ∩ S_m) = <delta_J, A_m delta_(Jz)> <= ||A_m||`.
- **Left cosets.** `S_m = S_m^(-1)` and `(yJ)^(-1) = J y^(-1)`, so
  `#(yJ ∩ S_m) = #(J y^(-1) ∩ S_m)`.

Together these give item 1 of the target:
`#(yJ ∩ S_m) <= (1 + 1/q)(m+1) r_J^m` for every `y` and every `m`.

If `J` is not co-amenable, then part (a) of
`fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap` (with
`Gamma = Lambda`, `I = J`, `S = S_Lambda`) gives `rho_J < 1`. Then
`(q+1) rho_J < q+1`, and `r_J < q`: either `r_J = sqrt q < q`, or `mu_+` is
strictly increasing there and `mu_+(q+1) = q`.

Artifact part (a) verifies `A_n = P_n(A_1)` and the matrix-entry formula on a
random finite Schreier graph of `F_2`. Artifact part (c) shows that
`sup_y #(yJ ∩ S_m)` can strictly exceed `#(J ∩ S_m)`, for
`J = <a, bab^-1>` at `m = 2, 3, 7, 8, 9`. So a bound on `J` alone would not
suffice, and the operator norm is what makes the bound uniform.

## Step 4. Item 2: the section-growth barrier is co-amenability

Let `G = T x H` and `I <= Lambda x H_grp` be infinite, with `J = J(I)`.

**If `J` is not co-amenable, then `beta(I) <= r_J < q`.** Each nonempty
section is a left coset `I_h = y_h J`: this is stated in the setting of
`fpbs-tree-product-thin-section-subgroups-have-tilt-gap`, and it holds because
`(y,h), (y',h) in I` imply `(y^(-1) y', 1) in I`. By Step 3,
`sup_h #(I_h ∩ S_m) <= (1 + 1/q)(m+1) r_J^m`, so `beta(I) <= r_J`, and
`r_J < q` by Step 3.

The gap statement is then item 2 of
`fpbs-tree-product-thin-section-subgroups-have-tilt-gap`, quoted verbatim:

> Let `I` be infinite with `beta(I) < q`. Then for every `lambda in (0,1)`
> with `q^(max(lambda,1-lambda)) > beta(I)`,
> `p_c(G) < p_c(G,Gamma_xi,lambda) <= p_c(I;G)`.

The window stated in the target, `q^(max(lambda,1-lambda)) > r_J`, is
contained in this one because `beta(I) <= r_J`.

**Half tilt.** If `rho_J <= 2 sqrt q/(q+1)`, then `(q+1) rho_J <= 2 sqrt q`,
so `r_J = sqrt q`. Step 3 gives
`C' = sup_(h,m) #(I_h ∩ S_m)/((m+1) q^(m/2)) <= 1 + 1/q < infinity`. The same
item then gives `p_c(I;G) >= p_t` ("If `beta(I) < sqrt q`, or
`C' < infinity`, this gives `p_c(I;G) >= p_t`").

**If `J` is co-amenable, then `beta(I) = q`.**
- `J` is infinite by F5.
- On the tree, `tau_p(1,y) = p^(|y|)`. So
  `chi^J_p(T) = sum_m #(J ∩ S_m) p^m`.
- Apply `fpbs-co-amenable-subgroup-relative-threshold-is-pc` with
  `Gamma = Lambda`, `S = S_Lambda`, `I = J`. It gives
  `chi^J_p = infinity` for every `p > p_c(T) = 1/q`. So the power series has
  radius at most `1/q`, that is `alpha(J) >= q`.
- Always `alpha(J) <= q`, since `#S_m <= (q+1) q^(m-1)`.
- Finally `beta(I) >= alpha(J(I))`, since `I_1 = J`, and `beta(I) <= q`.

This proves `beta(I) < q` iff `J(I)` is not co-amenable.

## Step 5. Item 3 and the residual

**Item 3, the "only if" half.** If `I` is co-amenable, then Corollary 1 of
`fpbs-co-amenable-subgroup-relative-threshold-is-pc` gives
`p_c(I;G) = p_c(G)`. It also gives `chi^I_p = infinity` for all
`p > p_c(G)`, so the equality holds for either definition of `p_c(I;G)`.

**Item 3, the "if" half.** Let `Gamma = Lambda_1 x ... x Lambda_n x A` and
let `I` be infinite and not co-amenable. Let `iota_i` be the inclusion of the
`i`-th factor, and `J_i = iota_i^(-1)(I) <= Lambda_i`.
- Suppose every `J_i` is co-amenable in `Lambda_i`. By F3, `{1}` is
  co-amenable in `A`. By F2, `J_1 x ... x J_n x {1}` is co-amenable in
  `Gamma`. This is a subgroup of `I`, so by F1 `I` is co-amenable, which is a
  contradiction.
- So some `J_i` is not co-amenable. Put `H_grp = prod_(j != i) Lambda_j x A`,
  and let `H` be its Cartesian-product Cayley graph (trivial if `n = 1` and
  `A = 1`).
- Permuting coordinates is a group isomorphism `Gamma -> Lambda_i x H_grp`.
  It carries the product generating set onto `S_i ⊔ S_H`, and so it is a graph
  isomorphism `G -> T_i x H` carrying `I` to an isomorphic image `I'`. Both
  `p_c(G)` and `p_c(I;G)` are preserved.
- The tree section of `I'` is `J(I') = J_i`, which is not co-amenable.
- Since `I'` is infinite, Step 4 gives
  `p_c(G) < p_c(G, Gamma_xi, lambda) <= p_c(I;G)` for suitable `lambda`.

**Corollaries of item 3.**
- For normal `N`, co-amenable means `Gamma/N` amenable. One direction is F3.
  For the other, an invariant mean on `N\Gamma = Gamma/N` is an invariant mean
  on the group `Gamma/N`.
- Infinite amenable subgroups are not co-amenable, by part (b) of
  `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`, because
  `Gamma` is nonamenable: it has `Lambda_1` as a quotient, and quotients of
  amenable groups are amenable.

**Residual on `T x H`.** Let `I` be non-co-amenable with `J = J(I)`
co-amenable in `Lambda`, and let `K = I ∩ (1 x H_grp)`.
- *`H_grp` is nonamenable.* Otherwise `{1}` is co-amenable in `H_grp`
  (F3), so `J x 1` is co-amenable in `Gamma` (F2). It lies in `I`, so `I` is
  co-amenable (F1).
- *`K` is not co-amenable in `H_grp`.* The same argument applies with
  `J x K`.
- *Goursat.* `J` and `K` are normal in the projections `pi_1(I)` and
  `pi_2(I)`, and `(y,h) -> (yJ, hK)` induces an isomorphism
  `pi_1(I)/J ≅ pi_2(I)/K = Q`. This is standard: `I` is the graph of that
  isomorphism.
- *(R-slab) `Q` amenable.*
  - By F3, `J` is co-amenable in `pi_1(I)` and `K` in `pi_2(I)`. By F2,
    `J x K` is co-amenable in `pi_1(I) x pi_2(I)`, and then by F1 so is `I`.
  - By F1, `pi_1(I)` is co-amenable in `Lambda`, since it contains `J`.
  - If `pi_2(I)` were co-amenable in `H_grp`, then F2 would make
    `pi_1(I) x pi_2(I)` co-amenable in `Gamma`, and F4 would make `I`
    co-amenable. So `pi_2(I)` is not co-amenable.

These are the statements recorded in the target. No percolation statement is
claimed for the residual.

## Dependencies used

- `fpbs-tree-product-thin-section-subgroups-have-tilt-gap`, item 2 (quoted
  above), and its definitions of sections, `beta` and `p_c(I;G)`.
- `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`, parts (a) and
  (b).
- `fpbs-co-amenable-subgroup-relative-threshold-is-pc`: the Theorem and
  Corollary 1.
- Standard facts proved inline: F1–F5, the tree identities, Chebyshev
  polynomials, the spectral theorem for bounded self-adjoint operators, and
  Goursat's lemma.
