---
rg: 2
id: fpbs-relative-gap-along-any-subgroup-separates-proof
kind: route
title: Global uniqueness forces uniqueness along the subgroup, and relative sharpness turns the gap into finite relative susceptibility
target: fpbs-relative-gap-along-any-subgroup-separates
requires:
  - fpbs-hp-uniqueness-and-long-range-order
  - fpbs-hp-relative-sharpness
---

**The relative thresholds lie below `p_u(G)`.**
- `p_c(I;G) <= p_u(I;G)` holds because a unique I-infinite cluster is in
  particular an I-infinite cluster.
- Let `p > p_u(G)`. By definition of the infimum, some `p' < p` has a unique
  infinite cluster a.s. An infinite cluster is exactly a `Gamma`-infinite
  cluster, so `fpbs-hp-uniqueness-and-long-range-order` with `H = Gamma` gives
  `inf_{x,y in Gamma} tau_(p')(x,y) > 0`.
- The two-point function is increasing in `p`, so
  `inf_{x,y in I} tau_p(x,y) >= inf_{x,y in Gamma} tau_(p')(x,y) > 0`.
- The same theorem with `H = I` then gives a unique I-infinite cluster a.s. at
  `p`. Hence `p_u(I;G) <= p` for every `p > p_u(G)`.

**(1 ⇒ 2).** Choose `p` with `p_c(G) < p < p_c(I;G)`.
`fpbs-hp-relative-sharpness` gives an exponential tail for `|K_o ∩ I|`, so
`chi^I_p < infinity`.

**(2 ⇒ 1).**
- If `chi^I_p < infinity`, then `|K_o ∩ I| < infinity` a.s.
- For `h in I`, left multiplication by `h` is an automorphism of `G` that
  preserves the Bernoulli law and the set `I`. So `|K_h ∩ I|` has the law of
  `|K_o ∩ I|` and is finite a.s.
- An I-infinite cluster would contain some `h in I` with
  `|K_h ∩ I| = infinity`. By countability there is none a.s.
- The existence of an I-infinite cluster is increasing in `p` (monotone
  coupling), so none exists at any parameter up to `p`. Hence
  `p <= p_c(I;G)`, and `p > p_c(G)` by choice.

**Separation.** Under (1), `p_c(G) < p_c(I;G) <= p_u(G)`.

Amenability and wq-normality of `I` are used nowhere. In the existing
equivalence `fpbs-bs-iff-finite-relative-susceptibility` they are needed only
for the reverse inequality `p_u(G) <= p_c(I;G)`.
