---
rg: 2
id: fpbs-simon-lieb-gauge-certificates-die-at-pc
kind: claim
title: Left-invariant gauge-weighted Simon-Lieb certificates never hold at or above p_c on a Cayley graph
distinct_from:
  fpbs-spectral-dt-certificate-bounds-connectivity-operator: that shows the spectral certificate sp(nu_{U,p})<1 bounds the l2 connectivity operator and can hold only below p_{2->2}; this shows every weighted l1 certificate with a quasi-submultiplicative gauge fails at every p>=p_c, so spectral certificates are the l1-free survivors.
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

**ESTABLISHED (written deduction, self-contained; Section 2 of the artifact).**

Let `G = Cay(Gamma,S)` be a Cayley graph. Let `w : Gamma -> (0,infinity)`
satisfy `w(uv) <= K w(u) w(v)`, and let `U ∋ o` be finite. Put

```text
psi^w_p(U) = p sum_{(x,z) in partial U} tau^U_p(o,x) w(z).
```

**Claim.** `K psi^w_p(U) >= 1` for every `p >= p_c` and every finite `U ∋ o`.
If `K psi^w_p(U) < 1`, then:

- `sum_u tau_p(o,u) w(u) <= K sum_U w/(1 - K psi) < infinity`, and
- `p < p_c`.

For an arbitrary coarsely Lipschitz target `w`, the Simon–Lieb closure uses
the submultiplicative envelope `w^#(z) = sup_v w(zv)/w(v)`. That certificate
is `>= 1` at every `p >= p_c`, including for decaying targets such as
`exp(-t|u|)`. As a byproduct, `chi_p = infinity` for every `p >= p_c`.

**Class killed.** Left-invariant, gauge-weighted finite-volume l1 certificates
of tilted susceptibilities above `p_c`. Members include:

- the DCT mass;
- exponential gauges `exp(t|u|)`;
- polynomial gauges `(1+|u|)^D`;
- characters and quasimorphism exponentials;
- decaying gauges, through their envelopes.

**Invariant.** Inversion pairing `tau(o,u) = tau(o,u^{-1})` on a Cayley graph,
together with `w(u) w(u^{-1}) >= K^{-2}`, which closing the recursion forces.

**Step where every member dies.** The certified tilted sum dominates
`chi_p/K`, which is infinite for every `p >= p_c`.

**Survivors.**

- spectral l2 certificates;
- root-dependent cocycle tilts (horofunction, Radon–Nikodym);
- restricted target sums such as `sum_{h in H} tau_p(o,h)`;
- non-recursive geometric bounds.

On nonunimodular graphs the pairing carries the modular function, and the
obstruction is not claimed there.
