---
rg: 2
id: fpbs-fibre-truncation-pu-lower-semicontinuous-proof
kind: route
title: Uniqueness on a large truncation puts theta squared on every fibre point, which the lifted coupling forbids below p_u(G)
target: fpbs-fibre-truncation-pu-lower-semicontinuous
requires:
  - fpbs-fibre-truncation-towers-add-no-slack
  - fpbs-amenable-wq-normal-pu-is-relative-pc
  - fpbs-hp-relative-sharpness
  - fpbs-cluster-count-trichotomy
artifacts:
  - research/artifacts/fpbs-fibre-truncation-towers-2026-09-17.md
---

Details are in Section 3 of the artifact.

**Quantitative form.** Let `k >= k_1` with
`[H:H_k] theta_(G_(k_1))(p)^2 > chi^H_G(p)`, and suppose `p > p_u(G_k)`.

1. By `fpbs-cluster-count-trichotomy`, the infinite cluster of `G_k` is unique
   a.s. at `p`.
2. Fix `x in pi_k(H)`. Harris--FKG for the increasing events
   `{o <-> infinity}` and `{x <-> infinity}`, together with uniqueness, gives
   `tau^(G_k)_p(o,x) >= theta_(G_k)(p)^2`.
3. Item 3 of `fpbs-fibre-truncation-towers-add-no-slack` gives
   `theta_(G_k)(p) >= theta_(G_(k_1))(p)`.
4. Summing over the `[H:H_k]` points of `pi_k(H)` gives
   `chi^(k)(p) > chi^H_G(p)`. This contradicts item 1 of that claim.

**Semicontinuity.** Let `p < p_u(G)`. Normal subgroups are wq-normal, so
`fpbs-amenable-wq-normal-pu-is-relative-pc` gives `p < p_c(H;G)`. Then
`fpbs-hp-relative-sharpness` gives `chi^H_G(p) < infinity`. There are two
cases.

* **If `p <= p_c(G_k)` for all `k`,** then `p_u(G_k) >= p_c(G_k) >= p`.
* **Otherwise,** pick `k_1` with `p > p_c(G_(k_1))`, so that
  `theta_(G_(k_1))(p) > 0`. Since `H` is infinite and the nested `H_k` have
  trivial intersection, `[H:H_k] -> infinity`. The quantitative form then
  gives `p_u(G_k) >= p` for all large `k`.

Since `p < p_u(G)` was arbitrary, `liminf_k p_u(G_k) >= p_u(G)`.

**Corollary.** If `p_c(G) < p_u(G)`, then
`liminf p_u(G_k) >= p_u(G) > p_c(G)`.
