---
rg: 2
id: fpbs-tree-projected-pu-l2-iff-square-root-law
kind: claim
title: On tree-projected Cayley graphs over an amenable normal kernel, p_{2->2} = p_u is exactly a non-strict square-root law for fibre hitting
distinct_from:
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that characterizes p_c < p_{2->2} by a critical sphere bubble; this characterizes p_{2->2} = p_u by a non-strict l^(2+) law below p_u, and says nothing at p_c.
  fpbs-sphere-fibre-operator-iff-critical-fibre-l2: that is an equivalence at p_c over every quotient; this concerns the whole interval below p_u, and needs the free quotient for cut submultiplicativity.
  fpbs-normal-coset-fibre-mass-power-improvement: that is the general power improvement over any normal subgroup; this applies it on tree-projected graphs to trade a non-strict exponent bound for L2 boundedness.
artifacts:
  - research/artifacts/fpbs-fibre-power-improvement-2026-09-17.md
---

**ESTABLISHED.** Let `N` be an infinite amenable normal subgroup of `Gamma` with
`Q = Gamma/N` free of rank `n >= 2`. Let `S` be a finite symmetric generating set
with `pi(S)` inside a free basis, its inverses and `1`, and put `G = Cay(Gamma,S)`.
This covers every graph of `fpbs-tree-projected-cayley-graphs-strict-thresholds`,
including rigid decorations such as `S_rig` in `F_2 x Z`. The following are
equivalent:

* **(a)** `p_{2->2}(G) = p_u(G)`;
* **(b)** for every `p < p_u` and every `r > 2`,
  `sum_(q in Q) P_p(o <-> Gamma_q)^r < infinity`;
* **(c)** `liminf_(p -> p_u^-) r*(p) <= 2`, where `r*(p) = inf{r : sigma_p ∈ l^r(Q)}`.

Moreover, unconditionally,

```text
p_{2->2}(G) >= sup_(p' < p_u) (p')^(max(r*(p'),2)/2).
```

**Structure.**
* Below `p_u`, `||T_p|| < infinity` iff `sigma_p ∈ l2(Q)`:
  * block domination: `||T_p|| <= ||lambda_Q(sigma_p)||`;
  * a Følner lower bound: `||T_p||^2 >= ||sigma_p||_2^2`;
  * cut submultiplicativity with Haagerup's inequality.
* `fpbs-amenable-wq-normal-pu-is-relative-pc` gives `p_u = p_c(N;G)`.
* `fpbs-normal-coset-fibre-mass-power-improvement` upgrades a non-strict exponent
  2 to a strict one at every smaller parameter.

So Question Q of `research/artifacts/fpbs-amenable-normal-fibre-mass-bound-2026-09-16.md`
§5.2 is, on these graphs, the fibre-summed square-root law. This is the
backscattering statement `beta* >= 1/2` of Hutchcroft--Pan arXiv:2412.15895, and
their strictness step is no longer needed. Assuming (b), the hole
`fpbs-amenable-wq-normal-relative-subcriticality` on these graphs is equivalent to
critical L2, and hence to a critical sphere bubble below one.

Proof: artifact Lemmas 3.1, 3.2, 4.1, 4.2 and Theorem 3.

## Attempts

* **Block Schur test, Følner lower bound, cut submultiplicativity (2026-09-17,
  artifact §3–4).** The full proof is in the artifact. The remaining open input,
  whether (b) actually holds, is recorded in
  `fpbs-tree-projected-square-root-fibre-law-below-pu`.
