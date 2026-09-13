---
rg: 2
id: leavitt-unit-bounded-block-triviality-via-mf-radical
kind: route
title: Freeze the permutation skeleton, turn HS defects into operator defects on most blocks, and kill the labels by full MF radical
target: leavitt-unit-bounded-block-models-are-asymptotically-trivial
requires:
  - leavitt-units-admit-no-bounded-block-monomial-hs-model
  - binary-leavitt-all-ranks-full-mf-radical
---

**Notation.**  Write `rho_m(g)(e_x ⊗ v) = e_(sigma_g(x)) ⊗ u_m(g, sigma_g(x)) v`
with `sigma_g = sigma_(m,g)` in `S_(n_m)` and `u_m(g, y)` in `U(k_m)`.  On
`M_k` put `||X||_(2,k)^2 = (1/k) Tr(X^* X)`, so that
`||X||_op <= sqrt(k) ||X||_(2,k)` and `||X||_(2,k) <= ||X||_op`.

**(0) The skeleton is frozen.**  By
`leavitt-units-admit-no-bounded-block-monomial-hs-model` clause 1 (arbitrary
block sizes, no trace hypothesis), for every nonprincipal ultrafilter `omega`
and every `g`, `lim_omega d_H(sigma_(m,g), id) = 0`.  A bounded sequence whose
every `omega`-limit is `0` tends to `0`, so `mu_m(g) := d_H(sigma_(m,g), id) -> 0`.

**(1) Label defects on fixed blocks.**  Let `F_m(g,h)` be the set of blocks
fixed by `sigma_g`, `sigma_h` and `sigma_(gh)`.  For `x` in `F_m(g,h)`, the
column blocks at `x` of `rho(gh)` and `rho(g) rho(h)` are
`e_x ⊗ u(gh,x)` and `e_x ⊗ u(g,x) u(h,x)`.  Summing over those columns,

```text
(1/n_m) sum_(x in F_m(g,h)) ||u(gh,x) - u(g,x) u(h,x)||_(2,k_m)^2 <= eps_m(g,h)^2.
```

By `||X||_op^2 <= k ||X||_(2,k)^2` and Markov, the fraction of `x` in
`F_m(g,h)` with `||u(gh,x) - u(g,x)u(h,x)||_op >= 1/L` is at most
`L^2 k_m eps_m(g,h)^2`, which tends to `0` for each fixed `L` by (BB).  The
complement of `F_m(g,h)` has density at most `mu_m(g) + mu_m(h) + mu_m(gh) -> 0`.

**(2) A persistent label.**  Suppose `||rho_m(s) - 1||_2^2 >= c > 0` along a
subsequence.  The column blocks at unmoved `x` give
`||rho_m(s) - 1||_2^2 <= (1/n) sum_(sigma_s x = x) ||u(s,x) - 1||_op^2 + 4 mu_m(s)`.
Since each `||u(s,x) - 1||_op <= 2`, once `mu_m(s) <= c/8` the set
`B_m = {x : sigma_s x = x, ||u(s,x) - 1||_op >= sqrt(c)/2}` has density at
least `c/16`.

**(3) Extracting an operator-norm asymptotic representation.**  Enumerate the
pairs `(g_i, h_i)` of `U`.  For each `L`, (0) and (1) give `m_L` in the
subsequence, increasing in `L`, such that the good set

```text
G_L = { x : x in F_(m_L)(g_i,h_i) and ||u(g_i h_i,x) - u(g_i,x) u(h_i,x)||_op < 1/L for all i <= L }
```

has density `> 1 - c/32`.  Pick `x_L` in `B_(m_L) ∩ G_L` and set
`phi_L(g) = u_(m_L)(g, x_L)` in `U(k_(m_L))`.  Every pair `(g,h)` is eventually
among the first `L` pairs, so `||phi_L(gh) - phi_L(g) phi_L(h)||_op -> 0` as
`L -> infinity`.  Hence

```text
Phi : U -> U( prod_L M_(k_(m_L))(C) / bigoplus_L M_(k_(m_L))(C) ),   Phi(g) = [ (phi_L(g))_L ],
```

is a homomorphism into the unitary group of a norm matrix corona, and
`Phi(s) != 1` because `||phi_L(s) - 1||_op >= sqrt(c)/2` for every `L`.  Its
image is an MF group by definition.

**(4) Contradiction.**  By `binary-leavitt-all-ranks-full-mf-radical`, every
homomorphism from `U` to an MF group is trivial, so `Phi(s) = 1`.  This
contradicts (3), so `||rho_m(s) - 1||_2 -> 0`.

The fixed-`k` case needs no separate argument, since (BB) is automatic there.
Nothing uses the trace of `rho_m`, and injectivity is not assumed.

**Why the threshold is where the argument stops.**  Step (1) is the only
place the block size enters, through `||X||_op <= sqrt(k) ||X||_(2,k)`.  When
`k_m eps_m^2` stays bounded away from `0`, most blocks can carry labels that
are Hilbert--Schmidt approximate but not operator-norm approximate
representations, and full MF radical says nothing about those.  Deciding that
regime is exactly `binary-leavitt-unit-group-hyperlinear`.
