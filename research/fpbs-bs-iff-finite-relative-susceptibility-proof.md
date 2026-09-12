---
rg: 2
id: fpbs-bs-iff-finite-relative-susceptibility-proof
kind: route
title: Place a parameter below the relative critical threshold and use relative sharpness and translation invariance along H
target: fpbs-bs-iff-finite-relative-susceptibility
requires:
  - fpbs-amenable-wq-normal-pu-is-relative-pc
  - fpbs-hp-relative-sharpness
---

**(1 ⇒ 3).** By `fpbs-amenable-wq-normal-pu-is-relative-pc`,
`p_u(G) = p_c(H;G)`. If `p_c(G) < p_u(G)`, pick `p` strictly between them.
Then `p < p_c(H;G)`, and `fpbs-hp-relative-sharpness` gives
`P_p(|K_o ∩ H| >= n) <= exp(-cn)`.

**(3 ⇒ 2).** Sum the tail.

**(2 ⇒ 1).** If `chi^H_p < infinity` then `|K_o ∩ H|` is finite almost surely.
For `h in H`, left multiplication by `h` is a graph automorphism of `G` that
preserves the Bernoulli law and the set `H` and maps `o` to `h`, so
`|K_h ∩ H|` has the law of `|K_o ∩ H|` and is finite a.s. An H-infinite cluster
would contain some `h in H` with `|K_h ∩ H| = infinity`; by countability no
H-infinite cluster exists a.s. The existence of an H-infinite cluster is an
increasing 0-1 event, so `p <= p_c(H;G) = p_u(G)`, while `p > p_c(G)` by
hypothesis. Hence `p_c(G) < p_u(G)`.

Nonamenability of `G` is not used; for amenable `Gamma` both sides are false.
