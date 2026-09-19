---
rg: 2
id: fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold
kind: claim
title: The replica meet limit lies between the exponential decay threshold and every amenable relative threshold, so it equals p_u wherever p_exp = p_u, including one-ended planar graphs and tree products
distinct_from:
  fpbs-replica-meet-threshold-sandwich: that gives p_c <= p_k <= p_cap^(k) <= p_u; this adds the lower bound p_exp <= sup_k p_k, which pins the limit to p_u on every graph with p_exp = p_u
  fpbs-meet-threshold-capped-by-amenable-relative-threshold: that caps p_cap^(k) above by p_c(H;G); this bounds it below by p_exp and concludes p_c(H;G) = p_u for all infinite amenable H whenever p_exp = p_u
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that is an open kernel about one rare pair per ball; this is an established comparison of the meet thresholds with the uniform decay threshold p_exp
  fpbs-replica-meet-cap-inf-fails-free-products: that refutes p_cap^(infty) = p_u on A * Z/2; this proves it on every graph with p_exp = p_u
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

**ESTABLISHED.** Route `fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold-proof`.

Let `G = Cay(Gamma,S)` be a finitely generated Cayley graph. Use the notation
of `fpbs-replica-meet-threshold-sandwich`:

- `Z_k(p) = sum_x tau_p(o,x)^k` and `p_k = sup{p : Z_k(p) < infinity}`;
- `p_cap^(k) = sup{p : |M_k(o)| < infinity a.s.}` and
  `p_cap^(infty) = sup_k p_cap^(k)`.

Let `p_exp` and `xi_p` be as in `fpbs-exp-decay-threshold-facts`, and let
`gr(G) = lim (1/n) log |S_n|`.

1. **Rate criterion.** `Z_k(p) < infinity` whenever `k xi_p > gr(G)`. This is
   sharp on `T_d`, where it reads `p < (d-1)^{-1/k} = p_k(T_d)`.
2. **Exponential sandwich.** `p_exp <= sup_k p_k <= p_cap^(infty) <= p_u`.
3. **Amenable form.** `p_exp <= p_cap^(infty) <= p_c(H;G) <= p_u` for every
   infinite amenable `H <= Gamma`.
4. **Conjecture 2.1 feeds the chain.** If `p_c < p_exp`, then some `p > p_c`
   and some `k` give `Z_k(p) < infinity`. Hence
   `fpbs-replica-meet-threshold-gap-universal` holds on `G`, and so does the
   relative gap along every infinite amenable subgroup.
5. **Equality classes.** If `p_exp = p_u`, then
   `p_cap^(infty) = sup_k p_k = p_u`, and `p_c(H;G) = p_u` for every infinite
   amenable `H`. This holds on:
   - (a) transitive one-ended nonamenable planar Cayley graphs, for example
     the standard Cayley graph of a closed surface group of genus at least 2.
     So on that graph every infinite cyclic subgroup has `p_c(H;G) = p_u`.
   - (b) `T x A` with `T` a `k`-regular tree (`k >= 3`) and `A` an infinite
     amenable Cayley graph. `T x A` is the Cayley graph of the direct
     product with the union of the generating sets. The same holds for the
     lamplighter `LL(T)` wherever Hutchcroft–Pan's `LL(T)` is a Cayley graph.
   - (c) regular trees.

Proof: Sections 1 and 2 of the artifact.
