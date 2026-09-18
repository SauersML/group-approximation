---
rg: 2
id: fpbs-lq-two-point-infinite-cluster-reduction
kind: claim
title: Above p_c the finite-cluster two-point function is in l^1, so every l^q threshold is decided by the infinite-cluster part, integer moments are intersections of independent infinite clusters, and one finite exponent forces a positive worst-pair rate
distinct_from:
  fpbs-lq-threshold-power-monotonicity: that relates different exponents and parameters by thinning; this removes the finite-cluster part at a fixed parameter and ties a single finite exponent to the worst-pair rate, and uses the Hermon--Hutchcroft input that the thinning node does not use.
  fpbs-two-point-fourier-algebra-criterion: that puts tau^fin in the Fourier algebra A and bounds the singular mass by theta; this puts tau^fin in l^1 (a summability statement A does not give) and reduces the l^q thresholds, not A-membership, to tau^inf.
  fpbs-worst-pair-connectivity-rate-kernel: that proves (K) implies p_c < p_u and that the sphere rate forces (K); this proves that any finite l^q exponent at one p forces (K) with the explicit rate log(gr)/q.
  fpbs-supercritical-finite-susceptibility: that is the imported finiteness of chi^fin; this is its consequence for the whole l^q scale.
artifacts:
  - research/artifacts/fpbs/docs/lq-infinite-cluster-reduction-2026-09-18.md
---

**ESTABLISHED.** Proof in `fpbs-lq-two-point-infinite-cluster-reduction-proof`
(Sections 1–3 of the artifact).

Let `G` be a connected, locally finite, transitive, nonamenable graph,
`tau^fin_p(o,x) = P_p(o <-> x, |K(o)| < infinity)`,
`tau^inf_p = tau_p - tau^fin_p`, `Z_q = sum_x tau_p(o,x)^q`,
`Z^inf_q = sum_x tau^inf_p(o,x)^q`, and `p_q`, `q_0` as in
`fpbs-lq-threshold-power-monotonicity`.

**Claim.**

1. **(A) Finite part in l^1.** For every `p > p_c` and `q >= 1`,
   `sum_x tau^fin_p(o,x)^q <= chi^fin(p) < infinity` and
   `Z^inf_q <= Z_q <= 2^(q-1)(chi^fin(p) + Z^inf_q)`. Hence
   `Z_q(p) < infinity` iff `Z^inf_q(p) < infinity`, and `q_0` and every
   threshold `p_q` are determined by `tau^inf` alone.
2. **(B) Intersection form.** For every integer `k` and every `p`,
   `Z^inf_k(p) = E_(p^k)|K^1_inf(o) ∩ ... ∩ K^k_inf(o)|` for independent
   configurations. The same holds for `Z_k` without the subscript `inf`. On `T_d`
   the intersection is the `p^k`-cluster of `o`.
3. **(C) One exponent gives the worst-pair kernel.** If `Z_q(p) < infinity` for
   some `q < infinity`, then `gamma(p) >= log(gr)/q` (notation of
   `fpbs-worst-pair-connectivity-rate-kernel`),
   `limsup (1/n) log E_p[|K(o) ∩ B_n|; |K(o)| = infinity] <= (1 - 1/q) log gr`,
   and `P_p` has no unique infinite cluster.

**Consequences.** `[Q] => q_0 < infinity => (K) => p_c < p_u`. The middle
statement is the new hole `fpbs-two-point-some-lq-above-pc-universal`.
