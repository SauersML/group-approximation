---
rg: 2
id: fpbs-malnormal-coset-cycles-linear-perimeter
kind: claim
title: Over a finitely generated malnormal subgroup of a free group, coset cycles have perimeter linear in the number of new edges, so detour packing has finite growth and a positive floor
distinct_from:
  fpbs-malnormal-coset-cycles-bounded-syllables: that bounds each syllable by O(k), hence the perimeter only by O(k^2), and leaves the packing growth h undecided; this bounds the whole perimeter by O(k), proves h < infinity, and gives an explicit positive floor for every packing certificate.
  fpbs-malnormal-subgroup-relations-finite-contacts: that counts direct contacts between subgroup classes in a graphing; this is a group-theoretic count of multi-step coset cycles, with no graphing.
artifacts:
  - research/artifacts/fpbs-malnormal-coset-cycles-linear-perimeter-2026-09-17.md
---

Let `F` be free with basis `S`, `r = |S|`, let `H <= F` be finitely generated
and malnormal, `m` the number of vertices of its based Stallings graph,
`D = m^2`, and `t in F \ H` with `τ = |t|_S`. Use the coset graph and detours
of [[fpbs-malnormal-coset-cycles-bounded-syllables]].

1. **Linear perimeter.** A simple coset cycle with `k` `t`-edges and syllables
   `h_i` satisfies

       sum_i |h_i|_S + k τ  <=  B (4k - 3) max(D, τ),
       B = (2r)^(2D+2) + 2τ.

2. **Finite growth.** Put `c = 4 B max(D, τ) + 2` and `A = (2r+3)^c`. The number
   `M(k)` of simple cycles through a fixed edge `e(g)` with `k` `t`-edges is at
   most `A^k`. So every edge-disjoint detour family for `e(g)` has packing count
   `N(R) <= sum_{j <= R+1} A^j`, and `h <= log A < infinity`.
3. **Positive floor.** For every `q in (0,1]` and every edge-disjoint detour
   family with `k_i` `t`-edges,

       q + (1-q) prod_i (1 - q^(k_i))  >=  δ := 1 / (8 A^2).

   So the packing bound (2.1) of `research/artifacts/fpbs/small-cancellation-family.md`,
   read for arbitrary detour words, never certifies `relC(E_F; E_H) < δ`.
4. **Uniform floor for `Gamma_mal`.** In `Gamma_mal = lim(F_2 -> F_2)`,
   `a -> a`, `b -> b a b^{-2}`, write `H_m = <a, b_m>`. For all `n < m`,
   `H_m = <H_n, b_m>`. Every packing certificate for `relC(H_m; H_n)` with new
   generator `b_m`, or with any generator in `H_n b_m^{±1} H_n`, is at least
   the constant `δ_mal = δ(F_2, <a, b a b^{-2}>, b)`, with Stallings size 3,
   `D = 9`, `τ = 1`.

**The invariant and the step.**
- **Invariant.** The linear perimeter constant `B max(D, τ)`.
- **Step.** The divergence step (2.3)–(2.5) of the packing lemma needs
  `sum_i q^(k_i) = infinity` for small `q`. Item 2 makes that sum finite below
  `1/A`. So both the stage-sum strategy `C <= 2 + sum_n relC(H_{n+1}; H_n)` and
  the subsequence strategy `relC(H_m; H_n) -> 0`, when certified by packing
  with `b_m`, are dead for `Gamma_mal`.

**Not claimed.**
- No lower bound on `relC` itself.
- Nothing is claimed about packing with generators `t'` outside
  `H_n b_m^{±1} H_n`. There `τ'` is unbounded, and so is the floor's
  dependence on it. See [[fpbs-mal-long-generator-packing-growth]].

## Attempts
