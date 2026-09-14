---
rg: 2
id: numeric-window-relations-do-not-force-balance-proof
kind: route
title: Følner entropy count for amenable decoders, and merge and AND measures with small interiors for nonamenable ones
target: numeric-window-relations-do-not-force-balance
requires: []
artifacts:
  - research/artifacts/numeric-window-relations-no-go-2026-09-12.md
---

A complete direct proof is in the artifact.

- **Amenable case (Proposition 1).**
  - Along right Følner sets `F_k` of the decoder memory group, `|F_k \ int_N F_k| = o(|F_k|)`.
  - R3 bounds every pattern probability on `F_k` by `q^(-|int_N F_k|)`, so the Shannon entropy on `F_k` is at
    least `|int_N F_k| log q`.
  - Subadditivity bounds that entropy by `|F_k|` times the site entropy. So the site entropy is `log q`, and
    the site law is uniform.
- **Nonamenable interiors (Lemma 2).**
  - Følner's criterion gives `|FN| >= (1 + eps)|F|` on the subgroup, and then on all of `G` coset by coset.
  - Since `int_N E` times `N` lies in `E`, `|int_N E| <= |E|/(1 + eps)`.
- **Merge measure (Theorem 3).**
  - The rule `f(a_2) = a_1` gives an iid measure with atoms `2/q`, `0` and `1/q`.
  - The counts `q^(|EM|-|E|) 2^#{p = a_1}` are integers, and `{x(e) = a_2}` is null.
  - `nu[p]_E <= (2/q)^|E| <= q^(-theta_N|E|) <= q^(-|int_N E|)` once `q^(1-theta_N) >= 2`.
- **AND measure (Proposition 4).**
  - Transfer matrices `T_0 = [[1,1],[1,0]]` and `T_1 = [[0,0],[0,1]]` bound each run of `l` sites on a coset
    of `<c>` by `(phi_g/2)^l`, where `phi_g` is the golden ratio. Runs and cosets are independent, so
    `nu[p]_E <= 2^(-0.3057|E|)`.
  - In the 4-regular tree, degree counting in the induced forest gives `|int_(B_1) C| <= |C|/3`, hence
    `|int_(B_2) C| <= |C|/9`.
  - Splitting along cosets of the free pair gives `|int_N E| <= |E|/9`.
  - The pattern `(1,0,1)` along `c` is null.
