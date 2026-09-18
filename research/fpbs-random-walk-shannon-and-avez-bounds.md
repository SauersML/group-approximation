---
rg: 2
id: fpbs-random-walk-shannon-and-avez-bounds
kind: claim
title: A symmetric finitely supported walk on a nonamenable group has positive entropy and concentrates on its level set
distinct_from:
  kesten-amenable-stabilizer-uniform-gap: that records the Kesten spectral radius and a Dirichlet gap on coset spaces; this records the Avez entropy lower bound and the Shannon–McMillan–Breiman theorem for the walk itself.
---

**ESTABLISHED (citation import).** Let `Gamma` be a countable group and `mu` a
symmetric probability measure on `Gamma` with finite support. Let
`X_n = xi_1 ... xi_n` with `xi_i` i.i.d. of law `mu`, so `X_n` has law
`mu^{*n}` and `p_n(e, g) = mu^{*n}(g)`. Let `rho_LP = limsup_n p_n(e,e)^{1/n}`.

1. **Avez entropy.** `h = lim_n H(X_n)/n` exists, and `h >= 2 log(1/rho_LP)`.
   In particular `rho_LP < 1` implies `h > 0`.
2. **Shannon–McMillan–Breiman.** Almost surely
   `-(1/n) log mu^{*n}(X_n) -> h`. Hence for every `eta > 0`,

```text
pi_n(eta) := P( | -(1/n) log mu^{*n}(X_n) - h | > eta )  ->  0.
```

3. If `Gamma` is nonamenable and `mu` is uniform on a finite symmetric
   generating set `S`, then
   `rho_LP <= ||lambda(mu)|| < 1`, so `h > 0`. The first inequality holds
   because `p_n(e,e) = <lambda(mu)^n delta_e, delta_e> <= ||lambda(mu)||^n`.
   The second is Kesten's theorem as recorded in
   `kesten-amenable-stabilizer-uniform-gap`.

A random walk on a group is a transitive symmetric Markov chain, and
`H(X_1) < infinity` because the support is finite. So items 1 and 2 are
Proposition 14.6 and Theorem 14.10(ii) of Lyons–Peres. Proof:
`fpbs-random-walk-shannon-and-avez-bounds-citation`.
