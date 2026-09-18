---
rg: 2
id: fpbs-pu-open-certificates-pinned-at-pc
kind: claim
title: p_u is not local, and every ball-local nonuniqueness certificate certifies only p at most p_c on local limits of amenable groups
distinct_from:
  fpbs-l2-gap-class-closed-under-local-limits: that treats the operator threshold Gamma_M under local limits; this is about p_u itself and about every open certificate, and it adds the free-solvable tower converging to F_2 where p_u jumps from about 1/3 to 1.
  fpbs-easo-hutchcroft-pc-locality: that is continuity of p_c; this shows p_u is neither lower nor upper semicontinuous and uses p_c continuity to pin open p_u certificates at p_c.
  fpbs-pu-nonuniqueness-cannot-separate: that concerns what nonuniqueness at p_u can separate; this is about local certifiability of nonuniqueness above p_c.
artifacts:
  - research/artifacts/fpbs-pu-nonlocality-2026-09-17.md
---

**ESTABLISHED** through `fpbs-pu-open-certificates-pinned-at-pc-proof`.
Work in the compact space `M_d` of `d`-marked groups with the local
(ball) topology, and `X = M_d x [0,1]`.

**(A) p_u is not local.** Let `S_k = F_2/F_2^(k)` (derived series), marked by
`a,b`. Then `S_k -> F_2`, `p_u(S_k) = p_c(S_k) <= 1/2`, and
`p_u(S_k) -> 1/3 = p_c(F_2)`, while `p_u(F_2) = 1`. So `p_u` is not lower
semicontinuous, and the gap `p_u - p_c` is not lower semicontinuous at `F_2`.
`Z x C_k -> Z^2` with `p_u = 1 -> 1/2` shows `p_u` is not upper semicontinuous.

**(B) Pinning.** Let `A_d` be the set of local limits of infinite amenable
marked groups with `p_c != 1`. Let `U subseteq X` be open, and sound on the
infinite amenable groups in some ball-neighbourhood of `G`: `(G',p) in U`
implies `p <= p_u(G')`. Then for `G in A_d`, `(G,p) in U` implies
`p <= p_c(G)`. Equivalently, no sound certificate is a neighbourhood of
`(G,p)` with `p > p_c(G)`. Any certificate of `p_c(G) < p_u(G)` there must use
a hypothesis that is not a neighbourhood of `G` in marked-group space, such as
`rho <= r < 1`, `h >= h_0`, `||T_q|| <= M`, or `lambda(q) <= r`.

**(C) The walk rate jumps.** For every `q in (1/3,1)`, `lambda(S_k,q) = 1` for
all large `k`, while `lambda(F_2,q) < 1`. So `{lambda(.,q) < 1}` is not open,
and the (IS)-type premises of `fpbs-integrated-sensitivity-universal` cannot
be verified from finite-ball data on `A_d`.

**Scope of A_d.**

* It contains every residually solvable group with a covering abelian marking
  of rank at least 2, for example `F_2`, surface groups and RAAGs.
* It contains `G x Z^2` for every LEA group `G`, for example every residually
  finite group.
