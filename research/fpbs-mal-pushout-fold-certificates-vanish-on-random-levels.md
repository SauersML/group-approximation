---
rg: 2
id: fpbs-mal-pushout-fold-certificates-vanish-on-random-levels
kind: claim
title: For the fold pair (L, K = <a, bab^-2>), the quotient of a level stabilizer N by the normal closure of K cap N is the one-vertex triangle group P_V = <t_v | t_v = t_{vc} t_{vcb}>; every finite group S gives a D0 certificate E >= log_|S| |Hom(P_V, S)|, and on uniformly random levels all these certificates are O(log n), with abelian S included, unconditionally
distinct_from:
  fpbs-mal-modp-promotion-certificates-are-fox-annihilators: that treats abelian (mod-p homology) certificates and, for towers, is conditional on Jaikin-Zapirain's conjecture; this gives the nonabelian presentation N/<<K cap N>> = P_V, a certificate for every finite group S (the case S = F_p recovers k_u), and an unconditional vanishing theorem on random levels for all S at once.
  fpbs-mal-bernoulli-single-stage-floor: that is the open target; this decides nothing about it and removes the finite-quotient counting certificates for its necessary part D0 on random levels.
  fpbs-mal-profinite-fold-density-is-finite-percolation: that is an upper bound (fold seeds, 2-of-3 percolation); here percolation appears only as the upper bound d(P_V) <= r(V), and the new content is the lower-bound side.
artifacts:
  - research/fpbs-mal-pushout-fold-certificates-vanish-on-random-levels-proof.md
  - experiments/fpbs-pushout-fold-group-2026-09-17/foldgroup.py
  - experiments/fpbs-pushout-fold-group-2026-09-17/verify_pushout.py
  - experiments/fpbs-pushout-fold-group-2026-09-17/small_regular.py
  - experiments/fpbs-pushout-fold-group-2026-09-17/small_regular_out.txt
  - experiments/fpbs-pushout-fold-group-2026-09-17/random_means.py
  - experiments/fpbs-pushout-fold-group-2026-09-17/random_means_out.txt
  - experiments/fpbs-pushout-fold-group-2026-09-17/random_means_abelian_out.txt
  - experiments/fpbs-pushout-fold-group-2026-09-17/random_out.txt
  - experiments/fpbs-pushout-fold-group-2026-09-17/regular_out.txt
---

**ESTABLISHED (Theorems A, B, C are unconditional; the census is evidence
only).** Proofs are in
`research/fpbs-mal-pushout-fold-certificates-vanish-on-random-levels-proof.md`.

**Setting.**
- `L = F(a, b)`, `c = b a b^-2`, `K = <a, c>`. Then `{b, c}` is a free basis
  of `L`, with `a = b^-1 c b^2`, and so is `{c, x}` with `x = cb = b a b^-1`.
- A *level* is a finite transitive right `L`-set `V`, `|V| = n`. `N` is the
  stabilizer of a base point `v0`, and `t` is the number of `K`-orbits.
- A *generating graph* `Y` at level `V` has
  - the `K`-Schreier graph `Y_K` (edges `v -> v.a` and `v -> v.c`), plus
  - `E` extra edges `v_i -> v_i.l_i` with labels `l_i` in `L`,
  - with `Y` connected and the labels of closed loops at `v0` generating `N`.
  This is exactly the finite-level object that bounds `Q_0 = relC(R_L; R_K)`
  in Theorem 2 of `fpbs-mal-modp-promotion-certificates-are-fox-annihilators`.
- For a finite group `S`, an *S-fold colouring* is `s : V -> S` with
  `s_v = s_{vc} s_{vcb}` for every `v`. `Z_S(V)` is the number of them.
- `P_V = < t_v (v in V) | t_v = t_{vc} t_{vcb} (v in V) >`. So
  `Z_S(V) = |Hom(P_V, S)|`.

**Theorem A (pushout presentation).** If `K` is transitive on `V`, then

```text
N / <<K cap N>>^N   =   P_V .
```

- For `V = L/N` with `N` normal, `L/<<K cap N>>^L` is the pushout `L *_K Q`,
  which is `<Q, b | b alpha b^-2 = gamma>` with `alpha, gamma` the images of
  `a, c`. It splits as `P_V x| Q`.
- The presentation complex of `P_V` has one vertex, `n` edges and `n`
  triangles. Each edge lies on exactly three triangles, and `chi = 1`.
- The relator `t_v = t_{vc} t_{vcb}` is the 2-of-3 fold rule. Hence
  `d(N | K cap N) >= d(P_V)`, and `d(P_V) <= r(V)`, the 2-of-3 percolation
  number.
- Its abelianization is `coker(1 - c - cb)` on `Z[V]`, the Fox element `u` of
  the mod-p node.

**Theorem B (counting certificate, every level, every S).** For every level
`V` (any `t`), every generating graph `Y` and every finite group `S`:

```text
E  >=  log_|S| Z_S(V).
```

- For `S = F_p` this is `E >= k_u(V)`, Theorem 1 of the mod-p node.
- Consequently, on every free profinite witness `X = lim V_m`,
  `Q_0(X) >= limsup_m log_|S| Z_S(V_m) / |V_m|`, by the same passage to clopen
  graphings as that node's Theorem 2. That passage uses only a lower bound on
  `E` valid for every generating graph at every level.

**Theorem C (annealed vanishing on random levels).** Let `b, c` be independent
uniform permutations of `[n]`. For every finite set `S` and every map
`F : S x S -> S`,

```text
E #{ s in S^n : s_v = F(s_{v.c}, s_{v.cb}) for all v }  <=  (n+1)^(|S|^2 + 2|S|).
```

Hence, for every finite group `S`, with probability at least `1 - 1/(n+1)`,

```text
log_|S| Z_S(V_n)  <=  (|S|^2 + 2|S| + 1) log_|S| (n+1)  =  O(log n).
```

- This includes `S = F_p`, where `log_p Z = k_u(V_n)`. So on random levels the
  mod-p class dies unconditionally, with no appeal to Lück approximation.
- It stays `o(n)` while `|S|^2 log n = o(n)`.
- Conditioning on any event of probability at least `delta` (for example `K`
  transitive) multiplies the failure probability by at most `1/delta`. The
  census estimates `P(K transitive)` as 0.72, 0.85, 0.93, 0.97, 1.00, 1.00 at
  `n` = 8, 16, 32, 64, 128, 256. This estimate is not proved.

**What this kills.**
- The w13 node left "nonabelian `d(N/M)` certificates" as a survivor for D0.
  By Theorem A, `N/M` is `P_V`.
- Every finite-quotient lower bound on `d(P_V)` of counting type
  (`d >= log_|S| |Hom(P_V, S)|`) is covered by Theorem B.
- Theorem C shows that on uniformly random levels each of them is `O(log n)`
  for fixed `S`. A given `S = S_n` is `o(n)` when
  `|S_n|^2 log n = o(n)`. Each statement holds with probability at least
  `1 - 1/(n+1)` per `S`. No union over all small groups is claimed.
- Random levels are the sofic models of the fold-seed census (contagious
  sets of density about 0.116, quoted in
  `fpbs-bernoulli-fold-seeds-have-density-at-least-2-25`). So a sofic
  (W-sof) proof of D0 cannot go through normal generation detected by finite
  quotients. It must use the gap between relative rank `d(N | K cap N)` and
  what finite quotients of `P_V` of size `n^{o(1)}` see.
- `P_V` is not trivial. It is sometimes infinite (an exact rational kernel of
  dimension 1, so `b_1(P_V) = 1`, on random levels with `n = 12`). When its
  abelianization is finite, its order is `e^{theta n}` with `theta` between
  0.04 and 0.26 in the census. On an `A_4`-regular level, `P_V` is perfect and
  maps onto `A_5`
  (`small_regular_out.txt`). So the class does not die for the trivial reason
  that `N = <<K cap N>>^N`.

**What survives.**
- Counting certificates on structured towers. On Cayley levels `V = Q`,
  `Z_S(Q)` grows with representation multiplicities: `Z_{C2}` is `2^13` on a
  `PSL_2(7)` level (`n = 168`), and `k_u(p=2) = 42` on `PSL_2(11)`, matching
  the mod-p census.
- Positivity along a free profinite tower would be a nonabelian analogue of
  the failure of Lück approximation. It is not decided here.
- The relative-rank gap `d(N | K cap N) - d(P_V)`, and D1, are untouched.

**Census (evidence, not proof).**
- Theorem A was checked against an independent count of `Hom(N, S)` killing
  `K cap N`, computed from the Schreier graph (`verify_pushout.py`). There
  were 120 (level, S) cases and 0 mismatches, with nonvacuous counts
  1, 3, 4 and 10.
- On random levels the empirical `E Z_S` is flat in `n`: about 2 for `C_2`
  and `C_3` up to `n = 256`, and about 6 to 8 for `S_3` up to `n = 32`. This
  is close to the number of subgroups of `S`. That would match a
  Gaussian refinement of the proof of Theorem C, with one `O(1)` term per
  subgroup `T`, where `p = ` Haar on `T`. The refinement is not proved.

