---
rg: 2
id: fpbs-uniform-l2-gap-forces-uniform-kesten-gap-on-towers-proof
kind: route
title: Test the truncated l2 operators on the finite truncated fibre and pass to the limit along the tower
target: fpbs-uniform-l2-gap-forces-uniform-kesten-gap-on-towers
requires:
  - fpbs-fibre-truncation-towers-add-no-slack
  - fpbs-expansion-thinning-threshold
  - fpbs-tree-normal-relative-threshold-is-inverse-cogrowth
---

Notation is that of the target. `tau^X_p(x,y) = P_p(x <-> y)` on a graph `X`,
and `T^X_p` is the kernel operator of `tau^X_p`, with the norm (0.1) of
`research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`. Put `d = |S|`.

## Item 1

**(a) The truncations are the right marked groups.** Fix `j_0` with
`H_(j_0) ∩ B_Gamma(2) = {1}`. It exists because the `H_j` are nested with
trivial intersection and `B_Gamma(2)` is finite. For `j >= j_0`, `pi_j` is
injective on `B_Gamma(2)`, so:

- `pi_j(s) != e` for `s in S`, and `pi_j` is injective on `S`;
- the simple Cayley graph of the marked group
  `(Gamma/H_j; pi_j(s_1),...,pi_j(s_k))` has generating set
  `{pi_j(s_i)^(+-1)} \ {e} = pi_j(S)`, of size `d`;
- so `G_j = Cay(Gamma/H_j, pi_j(S))` is `d`-regular, and simple random walk
  on `G_j` is the walk on `Gamma/H_j` driven by `mu_j`, the image of the
  uniform measure `mu` on `S`.

These are the covering quotients of `fpbs-fibre-truncation-towers-add-no-slack`
(its `k_0`).

**(b) Spectral radius does not increase along the tower.** Let
`psi_j : Gamma/H_j -> Q` be the quotient map, well defined since `H_j <= H`.
The image of the `mu_j`-walk under `psi_j` is the `mu_bar`-walk. Its
return event contains the image of the return event, so

```text
mu_j^(*n)(e) <= mu_bar^(*n)(e)   for all n,   hence   rho(G_j) <= rho_Q .
```

*Nonamenable `Q` gives `rho_Q < 1`.*

- Let `S'` be the set of nonidentity elements of `psi(S)`, where
  `psi : Gamma -> Q`, and let `nu` be uniform on `S'`. It is symmetric, and
  `S'` generates `Q`.
- Then `mu_bar >= (1/d) 1_(S') = c nu`, with `c = |S'|/d > 0`. So
  `mu_bar = c nu + (1 - c) lambda` for a symmetric probability measure
  `lambda`.
- As convolution operators on `l2(Q)`,
  `||P_(mu_bar)|| <= c ||P_nu|| + (1 - c)`.
- `P_nu` is simple random walk on the simple Cayley graph `Cay(Q,S')`. By
  Lemma 1.3 of `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`,
  `||P_nu||` equals its spectral radius. By Kesten's criterion (step 3 of
  Lemma 1.1 there), this is `< 1` when `Q` is nonamenable.
- Finally `mu_bar^(*n)(e) = <delta_e, P_(mu_bar)^n delta_e>` gives
  `rho_Q <= ||P_(mu_bar)|| <= c ||P_nu|| + 1 - c < 1`.

**(c) Finite test vector.** Let `j >= j_0`. `F := pi_j(H)` is a subgroup of
`Gamma/H_j` of order `[H : H_j] < infinity`.

- Left multiplication by `x` is an automorphism of `G_j`, so
  `tau(x,y) = tau(o, x^(-1) y)`.
- For `x in F`, `y -> x^(-1) y` permutes `F`. So
  `sum_(y in F) tau(x,y) = sum_(z in F) tau(o,z) = E_p |K^(G_j)_o ∩ F| = chi^(j)(p)`.
- Taking `f = g = 1_F` in (0.1),

  ```text
  ||T^(G_j)_p||  >=  <1_F, T 1_F> / |F|  =  (1/|F|) sum_(x in F) chi^(j)(p)  =  chi^(j)(p) .
  ```

  This holds in `[1, infinity]`, including when `T^(G_j)_p` is unbounded.

**(d) Pass to the limit.** Item 2 of `fpbs-fibre-truncation-towers-add-no-slack`
says `chi^(j)(p)` increases to `chi^H_G(p)`. With (c),

```text
chi^H_G(p) = sup_j chi^(j)(p) = lim_j chi^(j)(p) <= liminf_j ||T^(G_j)_p|| .
```

Together with (a) and (b), this is item 1.

## Item 2

Assume `rho_Q <= 1 - eta` and (U)`_(k,eta)(M,delta)`, and put
`delta' = min(delta, eta/(1+eta))`.

**(e) The parameter stays in `[0,1]`.**

- Take `j >= j_0`. By (b), `G_j` is the simple Cayley graph of a `k`-marked
  group with spectral radius at most `1 - eta`. So (U) applies to `G_j`.
- Let `h` be the edge expansion `inf |d_E A|/|A|` over finite nonempty vertex
  sets `A`, as in `fpbs-expansion-thinning-threshold`. The test function `1_A`
  gives `<P 1_A, 1_A> = |A| - |d_E A|/d`.
- So `||P|| >= 1 - |d_E A|/(d|A|)`, and with Lemma 1.3,
  `h >= d(1 - rho(G_j)) >= d eta >= eta`. The same bound holds for the
  degree-normalized expansion.
- By `fpbs-expansion-thinning-threshold`,
  `p_c(G_j) <= 1/(1+h) <= 1/(1+eta)`. Hence
  `p_c(G_j) + delta' <= 1/(1+eta) + eta/(1+eta) = 1`.

**(f) Uniform bound.**

- Item 3 of `fpbs-fibre-truncation-towers-add-no-slack` gives
  `p_c(G) <= p_c(G_j)`.
- `chi^(j)` is nondecreasing in `p`, since it is a sum of nondecreasing
  `tau`.
- Using (c), then (F1) of the local-limits note with `delta' <= delta` (this
  is the inclusion `U_{M,delta} ⊆ U_{M,delta'}` of Lemma 1.2 of the Baire
  artifact), then (U):

  ```text
  chi^(j)(p_c(G) + delta')  <=  chi^(j)(p_c(G_j) + delta')
                            <=  ||T^(G_j)_(p_c(G_j) + delta')||
                            <=  ||T^(G_j)_(p_c(G_j) + delta)||  <=  M .
  ```

  If `p_c(G_j) + delta > 1`, then the last two steps read as the definition
  of `U_{M,delta}`, which excludes such `G_j`. In that case (U) would be
  false, which is not the case assumed.
- Taking the sup over `j` in (d) gives `chi^H_G(p_c(G) + delta') <= M`.
- Finite `chi^H_G(p)` makes `|K_o ∩ H|` a.s. finite at `p`, and then at every
  smaller parameter by monotone coupling. So `H`-infinite clusters have
  probability `0` for `p <= p_c(G) + delta'`, and
  `p_c(H;G) >= p_c(G) + delta'`. QED item 2.

## Item 3

**(g) Apply item 2 to the tree.** Take `Gamma = F_2` with its free basis, so
`G = T`, `d = 4`, `p_c(T) = 1/3`, and `H = N`.

- `F_2` is residually finite. Let `K_j` be the intersection of all subgroups
  of index at most `j`. Then `H_j = N ∩ K_j` is a tower.
- The measure `mu_bar` is exactly the `mu` of
  `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth` with `q = 3`, so
  `rho_Q = rho_N`.
- The hypothesis `rho_N > sqrt(3)/2 = 2 sqrt(q)/(q+1)` is its standing
  assumption. Item 2 there gives `p_c(N;T) = s_N`, the unique `s` in
  `(0, 1/sqrt 3)` with `4 s/(1 + 3 s^2) = 1/rho_N`.
- That equation is `3 s^2 - 4 rho_N s + 1 = 0`. Its roots have product `1/3`,
  so the smaller root, `s_N = (2 rho_N - sqrt(4 rho_N^2 - 3))/3`, is the one
  below `1/sqrt 3`.
- If (U)`_(2,eta)(M,delta)` holds with `rho_N <= 1 - eta`, item 2 gives
  `1/3 + delta' <= p_c(N;T) = s_N`.

**The linear lower bound.** Write `rho_N = 1 - e`, with
`0 < e < 1 - sqrt(3)/2 < 1/4`. Then

```text
s_N - 1/3 - (2/3) e  =  ( 1 - 4e - sqrt(1 - 8e + 4e^2) ) / 3 .
```

- Both `1 - 4e` and `1 - 8e + 4e^2` are positive.
- `(1 - 4e)^2 - (1 - 8e + 4e^2) = 12 e^2 > 0`.
- So the numerator is positive, and `s_N - 1/3 > (2/3)(1 - rho_N)`.

Expanding, `sqrt(1 - 8e + 4e^2) = 1 - 4e - 6e^2 + O(e^3)`, so
`s_N - 1/3 = (2/3) e + 2 e^2 + O(e^3)`, and the ratio tends to `1`. As a
check, a direct numerical evaluation gives `(s_N - 1/3)/e` falling from `1.77`
at `rho_N = 0.866` to `0.667` as `rho_N -> 1`. QED item 3.

## Fixed-p remark in "What it changes"

**(h)** Let `p in (s_N, 1/sqrt 3)`. This interval is nonempty since
`s_N < 1/sqrt 3`.

- **Bounded on the tree.** On `T`, `tau_p(o,x) = p^|x|`, so `T^T_p` is right
  convolution on `F_2` by the radial function `f(x) = p^|x|`. Haagerup's
  inequality gives
  `||T^T_p|| <= sum_n (n+1) p^n |S_n|^(1/2)`, with `|S_n| = 4 * 3^(n-1)`.
  This is finite for `p sqrt 3 < 1`.
- **Unbounded along the tower.** By item 1 of the cogrowth node,
  `chi^N_p = infinity`. By (d), `liminf_j ||T^(G_j)_p|| >= chi^N_p = infinity`.
- **Local convergence.** `N_j ∩ B(r) = {1}` for large `j`, so `G_j -> T`
  locally.

So the map `G -> ||T^G_p||`, at a fixed `p` in `(s_N, 1/sqrt 3)`, is not
locally bounded at `T` in the space of 2-marked groups.

**Every fixed `p` in `(1/3, 1/sqrt 3)` is covered.** As `rho_N` increases to
`1`, `s_N` decreases to `1/3`. So it suffices to have normal subgroups `N_m`
of `F_2` with `rho_(N_m) < 1` and `rho_(N_m) -> 1`. They exist.

- Mark `F_2 = <a,t>`, and let
  `Gamma_m = < a, t | a^2, [a, t^i a t^(-i)] (1 <= i <= m) >`.
- `Gamma_m` is an HNN extension of `(Z/2)^(m+1)`, generated by
  `a, t a t^(-1), ..., t^m a t^(-m)`, with stable letter `t`. Its associated
  subgroups are the proper subgroups `(Z/2)^m`, spanned by the first `m` and
  by the last `m` generators.
- An HNN extension of a finite group is the fundamental group of a finite
  graph of finite groups, hence virtually free. Here the associated subgroups
  have index `2`, so the Bass–Serre tree is `4`-regular and has infinitely
  many ends. So `Gamma_m` is virtually nonabelian free, hence nonamenable. So by (b),
  `rho_(N_m) < 1`, where `N_m = ker(F_2 -> Gamma_m)`.
- `Gamma_m` converges, as a marked group, to the lamplighter
  `L = Z/2 wr Z`, marked by `(a,t)`.
  - `L` has the presentation `a^2`, `[a, t^i a t^(-i)]` for all `i >= 1`. That
    is the union of the presentations of the `Gamma_m`.
  - So `Gamma_m ->> Gamma_(m+1) ->> L`, and a word that is trivial in `L` is a
    consequence of finitely many relators, hence trivial in `Gamma_m` for
    large `m`.
  - Applied to the finitely many words of length at most `r`, this shows that
    the `r`-balls agree for large `m`. So `mu_bar^(*2n)(e)` agrees on `Gamma_m`
    and on `L` for `m` large, depending on `n`.
- On `L`, which is amenable, the Folner test functions `1_F` give
  `||P_(mu_bar)|| = 1`. The argument of Lemma 1.3 of the Baire artifact
  applies verbatim to symmetric convolution operators on a group, so
  `rho_L = 1`.
- As in step 1 of Lemma 1.1 there, `rho = sup_n mu_bar^(*2n)(e)^(1/(2n))`.
  So for each `n`, `liminf_m rho_(N_m) >= mu_bar_L^(*2n)(e)^(1/(2n))`, and the
  right side tends to `rho_L = 1` as `n -> infinity`.

So `rho_(N_m) -> 1`, and the fixed-p statement holds at every `p` in
`(1/3, 1/sqrt 3)`, as the target states.
