---
rg: 2
id: fpbs-two-point-some-lq-above-pc-universal
kind: claim
title: On every nonamenable Cayley graph some p above p_c and some finite k make the expected intersection of k independent infinite clusters of the origin finite
distinct_from:
  fpbs-two-point-lq-threshold-gap-universal: that is [Q], q_0 <= 2 (every q > 2 works just above p_c); this is only q_0 < infinity (one finite exponent at one p > p_c), which [Q] implies.
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that is (K), one exponentially rare pair per radius; this is a summability statement for the whole two-point function which implies (K) with rate log(gr)/k, and (K) does not imply it a priori.
  fpbs-two-point-in-fourier-algebra-near-pc-universal: that is A-membership, which carries no summability exponent; this is a summability exponent with no operator-algebra content.
artifacts:
  - research/artifacts/fpbs/docs/lq-infinite-cluster-reduction-2026-09-18.md
---

**OPEN ([Q_fin]).** Let `G` be a Cayley graph of a finitely generated
nonamenable group. Then some `p > p_c` and some integer `k >= 1` satisfy

```text
E_(p^k) | K^1_inf(o) ∩ ... ∩ K^k_inf(o) |  <  infinity ,
```

where the `K^i_inf(o)` are the clusters of `o` in `k` independent copies of
`P_p`, each set to the empty set when that cluster is finite.

**Equivalent forms.** By items (A) and (B) of
`fpbs-lq-two-point-infinite-cluster-reduction`, each of the following is
equivalent to [Q_fin]:

- `q_0 < infinity`, with `q_0` as in `fpbs-lq-threshold-power-monotonicity`;
- `sum_x tau_p(o,x)^q < infinity` for some `p > p_c` and some `q < infinity`;
- the same with `tau^inf_p` in place of `tau_p`.

**What it gives.**

- It gives (K) with `gamma(p) >= log(gr)/k`, by item (C) of the reduction claim.
- It therefore gives `p_c < p_u`, by
  `fpbs-bs-via-worst-pair-connectivity-rate`. The route is
  `fpbs-worst-pair-kernel-via-some-lq-two-point`.
- [Q] implies it (route `fpbs-some-lq-from-lq-threshold-gap`).

**Position.**

- **Trees.** On `T_d` the intersection of the `k` full clusters is the
  `p^k`-cluster of `o`. So `Z_k(p) = chi(p^k)`, which is finite iff
  `p^k < 1/(d-1)`. Hence [Q_fin] holds with `k = 2` at every
  `p in (p_c, (d-1)^(-1/2))`.
- **Collapse families.** The sharp dominating collapse families (H2/H5 of
  `fpbs-sharp-dominating-collapse-over-sparse-spines`) have the Bernoulli
  finite-cluster law and the Bernoulli `theta`. But their infinite cluster is
  unique, so `q_0 = infinity` for them.
  - By item (A), `Z_q` depends on the law only through `tau^fin` (always in
    `l^1`) and `tau^inf`.
  - So a proof of [Q_fin] must use Bernoulli structure of the infinite
    clusters that those families do not share.
  - Finite-cluster observables, `theta` and local laws cannot prove it
    (Section 6 of the artifact).

## Attempts

* **Russo–BK openness with the pivotal split (2026-09-18, swarm-0917-w9).**
  - Split the Russo derivative of `Z_q` into finite and infinite pivotal
    sides. The finite-side terms are then at most `C chi^fin(p) Z_q(p)`.
  - **Where it dies** (Section 5 of the artifact):
    - The Gronwall step needs `int chi^fin dp < infinity` near `p_c`, which
      already fails on `T_d`. Replacing it by an `l^r` bound is circular.
    - The pivotal term with both sides infinite is not controlled.
  - Transport from a known exponent by thinning
    (`fpbs-lq-threshold-power-monotonicity`) does not help either: it needs
    a finite exponent at some `p' > p_c` as input, which is [Q_fin] itself.
