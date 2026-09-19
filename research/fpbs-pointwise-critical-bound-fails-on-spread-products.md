---
rg: 2
id: fpbs-pointwise-critical-bound-fails-on-spread-products
kind: claim
title: No pointwise critical two-point bound of the form gr^(-alpha|x|) holds for any alpha > 0, already on Cayley graphs of F_r x Z with strict thresholds
distinct_from:
  fpbs-worst-pair-connectivity-rate-kernel: that bounds the infimum kappa_p(n) of tau_p over a ball, where Hutchcroft's critical bound kappa_(p_c)(n) <= gr^(-n) holds; this shows that the supremum over the same ball, along one explicit ray, decays at a rate independent of gr, so the infimum bound has no pointwise version.
  fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one: that proves equivalences between sphere-averaged l2 quantities under rapid decay; this shows that no pointwise growth-rate input can supply those quantities, so an RD proof must use the averaged form.
  fpbs-two-point-lq-threshold-gap-universal: that asks l^q summability of tau_p just above p_c; this is a pointwise lower bound at p_c on a thin ray, which is compatible with every l^q bound and only kills the pointwise route to it.
  fpbs-sphere-two-point-rate-below-arccosh-universal: that is a sphere-mass growth rate above p_c; this is a single-point lower bound at p_c along a ray and says nothing about sphere masses.
artifacts:
  - experiments/pointwise-critical-bound-2026-09-17/layered_lower_bound.py
  - experiments/pointwise-critical-bound-2026-09-17/layered_lower_bound.out
  - experiments/pointwise-critical-bound-2026-09-17/fibre_cluster.c
  - experiments/pointwise-critical-bound-2026-09-17/fibre_cluster_k100.out
---

**ESTABLISHED.** Proof in `fpbs-pointwise-critical-bound-fails-on-spread-products-proof`.

**Setting.** Let `H` be a finitely generated group with a finite symmetric generating set `S_H`, where `1 ∉ S_H` and `D = |S_H| >= 2`. Let `k` be even with `2k >= D`. Put

```text
X = Cay(H x Z, S),   S = S_H u {t^(+-1), ..., t^(+-k)},   d = |S| = D + 2k,
```

where `t` generates `Z`.

- `X` is the Cartesian product of `Cay(H, S_H)` with `Y_k = Cay(Z, {+-1, ..., +-k})`.
- Its word length is `|(h, t^m)| = |h|_(S_H) + ceil(|m|/k)`.
- Its growth rate is `gr(X) = gr(Cay(H, S_H))`.

The main case is `X_(r,k)`: here `H = F_r` with `S_H` a free basis and its inverses, so `D = 2r` and `gr = 2r-1`.

**Claim.**

1. **Ray bound.** For all `n >= 1`,

   ```text
   tau_(p_c)(o, t^(kn))  >=  100^(-n) / (D + 2k - 1),      |t^(kn)| = n.
   ```

   The constant 100 depends on nothing.
2. **No universal pointwise bound, with strict thresholds.** Fix `alpha > 0` and `C < infinity`. Take any `r` with `(2r-1)^alpha > 100` and any even `k >= r`. Then `X_(r,k)` violates

   ```text
   tau_(p_c)(o,x) <= C gr^(-alpha |x|)
   ```

   for all large `|x|` along the ray `t^(kn)`. The same holds for any bound `C gr^(-alpha|x| + o(|x|))`. In particular `tau_(p_c)(o,x) <= gr^(-|x|/2)` is false.
   - `p_c(X_(r,k)) < p_u(X_(r,k))`. The graph is a tree times a vertex-transitive graph, so the end-fixing subgroup of the tree times the translations of `Y_k` is a transitive nonunimodular subgroup, and `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` applies.
   - So the failure is not a symptom of `p_c = p_u`. It happens where Benjamini–Schramm is already a theorem.
   - Exact rational certificates for concrete finite instances are recorded in `layered_lower_bound.out`:
     - `r = 150`, `k = 20000`, `|x| = 60`, against `gr^(-|x|/2)`;
     - `r = 500`, `k = 10000`, `|x| = 25` and `|x| = 37`, against `gr^(-|x|/2)`;
     - `r = 10^5`, `k = 2*10^6`, `|x| = 52`, against `gr^(-|x|/4)`.
3. **One group suffices: `F_2 x Z`.** Take `H = F_2` and `S_H = B_L \ {1}`, the ball of radius `L` in the standard word metric. Then `gr = 3^L`.
   - Item 1 gives, on Cayley graphs of the single group `F_2 x Z`, the bound `limsup_n -(1/n) log tau_(p_c)(o, t^(kn)) <= log 100` while `log gr = L log 3 -> infinity`.
   - So even for one fixed group, the critical pointwise decay rate is not bounded below by any positive multiple of `log gr`, uniformly over generating sets.
   - This is the group of Choi–Seo Question 1.3 (`fpbs-product-every-generating-set`). Strict thresholds for these particular generating sets are not claimed.

**Consequences for the region (precise obstructions).**

- **Infimum does not become pointwise.** Hutchcroft's critical bound (arXiv:1605.05301v1, thm:pcconnectivitydecay) controls `kappa_(p_c)(n) = inf_(d(o,x) <= n) tau_(p_c)(o,x)`. Any argument that upgrades it to a pointwise bound `gr^(-alpha|x|)` using only transitivity, unimodularity and growth is refuted by item 2, since Cayley graphs are unimodular.
- **RD plus pointwise decay is dead.** Take the RD criterion (Theorem 1.1 of `research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md`) with trivial kernel, so the quotient is `Gamma` itself with RD exponent `D_RD`. Its input is `sum_x (1+|x|)^(2D_RD+2) tau_(p_c)(o,x)^2 < infinity`.
  - A pointwise bound `gr^(-alpha|x|)` with `alpha > 1/2` would give this sum from `|S_n| <= C_eps gr^((1+eps)n)`.
  - Item 2 excludes every such universal `alpha`.
  - So an RD proof of `p_c < p_(2->2)` must control the sphere-averaged quantity `b_n = sum_(|x|=n) tau^2` directly. This is the form in `fpbs-rd-weighted-bubble-iff-sphere-fibre-operator-below-one`.
- **Tempered-state and Cowling–Haagerup–Howe routes via pointwise decay are dead.** A universal `gr^(-alpha|x|)` bound with `alpha > 1/2` would put `tau_(p_c)(o,.)` in `l^(2+eps)`.
  - Item 5 of Part I of `fpbs-kazhdan-spectral-data-realized-by-fiid-collapse-proof` cites `tau_(p_c)(o,x) <= gr^(-|x|/2)` as "Hutchcroft's bound". That pointwise statement is false by item 2.
  - The conclusion drawn there, that the critical state is reduced, still follows from `theta(p_c) = 0` via Theorem I.1 of that route. So only the side remark is wrong.

**What this does not refute.**

- Graph-dependent exponential decay `tau_(p_c)(o,x) <= C e^(-c(G)|x|)`, which holds whenever `p_c < p_(2->2)`.
- Any `l^q` or sphere-averaged statement. The ray carries only `2k` points per shell.
- Hutchcroft's infimum bound. The infimum over a ball can be small, for example in the tree directions, while the ray value stays large.

## Attempts

* **Monte Carlo at r = 2 (calibration, heuristic only).**
  - An exact lazy-BFS sampler of the fibre cluster at `p = 1/(2k+3)` gives the following for `k = 100`, with 3*10^5 samples:
    - `P(0 <-> 100n)` is about 0.0238, 0.0097, 0.0049, 0.0023 and 0.00116 for `n = 1..5`;
    - the per-shell ratio is about 0.48, which is below `3^(-1/2) = 0.577`.
  - So at `r = 2` the fibre lower bound does not violate `gr^(-|x|/2)` in the sampled range.
  - Heuristically, a violation at `r = 2` would need `k` of order `10^3` and `|x|` of order 45. That is beyond sampling reach, and it is not claimed.
  - The rigorous violation uses large `r`.
