---
rg: 2
id: fpbs-amenable-wq-normal-pu-is-relative-pc-proof
kind: route
title: Relative Burton--Keane equates the relative thresholds and wq-normality equates relative and global uniqueness
target: fpbs-amenable-wq-normal-pu-is-relative-pc
requires:
  - fpbs-hp-relative-burton-keane
  - fpbs-hp-wq-normal-uniqueness-transfer
---

Since `H` is amenable, `fpbs-hp-relative-burton-keane` gives
`p_c(H;G) = p_u(H;G)`: there is never more than one H-infinite cluster, so the
first parameter at which one exists is the first at which it is unique.

Since `H` is wq-normal, `fpbs-hp-wq-normal-uniqueness-transfer` with
`H_1 = H` and `H_2 = Gamma` shows that a unique H-infinite cluster exists exactly
when a unique Gamma-infinite cluster exists. A Gamma-infinite cluster is an
infinite cluster, so `p_u(H;G) = p_u(G)`.

Combining, `p_u(G) = p_u(H;G) = p_c(H;G)`.
