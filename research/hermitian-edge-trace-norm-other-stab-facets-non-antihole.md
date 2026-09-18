---
rg: 2
id: hermitian-edge-trace-norm-other-stab-facets-non-antihole
kind: claim
title: The Hermitian edge trace-norm inequality holds at every full-support stable-set facet that is not a clique, an odd hole or an odd antihole
artifacts:
  - experiments/hermitian-edge-trace-norm-2026-09-18/README.md
distinct_from:
  hermitian-edge-trace-norm-other-stab-facets: that includes the odd-antihole rank facets; this excludes them.
  hermitian-edge-trace-norm-odd-antihole-facets: that is exactly the excluded family.
---

**OPEN (conjecture; numerics).** Let `(H, a)` be a full-support facet `a . x <= alpha_a(H)` of
`STAB(H)` other than (a complete graph, `a = 1`), (an odd hole, `a = 1`) and (an odd antihole,
`a = 1`). Then `||D C D||_1 >= sqrt3 (a(V(H)) - alpha_a(H))` for every admissible `C` on `H`, with
`D = diag(sqrt a)`.

Examples include the rank facets of webs and the facets of wheels with weighted hubs.
The local-minimisation ratios in `hermitian-edge-trace-norm-other-stab-facets` are between `1.155`
(`C_8^2`) and `1.239` (`W_7`).

## Attempts

- 2026-09-18 (w7-078), **tools that carry over.** Two of the odd-antihole tools
  (`hermitian-edge-trace-norm-odd-antihole-facets-by-size`) apply here without change:
  - the covering lemma `||C||_1 >= (1/lambda) sum_t ||C_{U_t}||_1`;
  - the kernel LP of its Step 3, which works on any circulant graph, i.e. the webs `C_n^k`, after
    changing the edge and non-edge distance sets in `cert_ah.py` and `verify_ah.py`.

  For a web the facet weight is still `a = 1`, so both tools apply directly. A facet with `a != 1`
  (wheels) needs a weighted matching `y` in (2).
- 2026-09-18 (w7-078), **the kernel LP falls short on the tested webs.** The float LP
  (`experiments/hermitian-edge-trace-norm-antihole-2026-09-18/cert_circ.py`, degree 4, no slack)
  reaches the following fractions of `sqrt3 (n - alpha)`:
  - `C_8^2`: `0.933`
  - `C_11^3`: `0.943`
  - `C_10^3`: `0.958`
  - `C_7^2 = C̄_7`: `0.970`

  On the same LP `C̄_13` reaches `1.014`. Presumably the loss comes from (R1) and from the AM-GM step
  (sharp only when `d_i = d_j` along the matching); this was not isolated. So webs need a different route, such as a
  covering by induced subgraphs with a certified minimum (as the house does for `C̄_7`), or the
  direct SDP branch-and-bound on the whole graph.
- 2026-09-18 (w7-078), **window coverings prove the webs `C_n^2`.** `hermitian-edge-trace-norm-web-rank-k2`
  (ESTABLISHED, computer-assisted) proves `||C||_1 >= sqrt3 (n - floor(n/3))` on `C_n^2` for every
  `n >= 8`. That covers every rank facet of those webs (a facet iff `3` does not divide `n`).
  - The `n` windows of six consecutive vertices induce `P_6^2` and cover each vertex 6 times.
  - Since `n - floor(n/3) <= 3n/4`, a single certified piece `c(P_6^2) >= 4.5 sqrt3` does every `n`
    at once. The branch-and-bound needs 1770 boxes.

  The same scheme works for any `k`. The numerical supremum of the needed window ratio
  `c(P_w^k)/(sqrt3 w)` over the webs with `n >= 2k+3` is `3k/(3k+2)`, attained at `n = 3k+2`. The
  numerical values of `c(P_6^3)` and `c(P_7^3)` are `0.832` and `0.833` of `sqrt3 w` (need `0.818`),
  so `k = 3` is within reach. For large `k` the windows must grow, because `3k/(3k+2) -> 1`.
- 2026-09-18 (w7-078), **clique windows prove the webs with `k >= 10`.** `hermitian-edge-trace-norm-web-rank-large-k`
  (ESTABLISHED; ordinary proof on certified clique bounds, exact arithmetic) proves the rank inequality
  `||C||_1 >= sqrt3 (n - floor(n/(k+1)))` on `C_n^k` for every `k >= 10` and every `n`. It also
  covers `k = 3` and `5 <= k <= 9` except finite lists of `n`, for example `k = 9` except `n = 29`.
  - The windows of `m = k + 1` consecutive vertices are cliques. The bound
    `c_m >= 2 (c_00 m^2 - m F(1))/(m-1)` from the large-m proof exceeds `sqrt3 (m-1)` by
    `eps_m >= sqrt3 (m-1)/(3m-1)` once `m >= 11`, and that margin handles every remainder `n mod m`.
  - This answers the concern above that the windows must grow for large `k`. Clique windows need no
    new certificate, because the margin `eps_m` of the large-m bound grows linearly in `m`.
  - Still open among webs: `k = 4` (it needs `c_5 > 4 sqrt3`) and the listed small-`k`, small-`n`
    pairs. The largest of those is `k = 5`, `n = 143`.
