---
rg: 2
id: fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels
kind: claim
title: Cayley graphs with a critical l2 gap satisfy all four pivotal kernels with bounded counts
distinct_from:
  fpbs-critical-l2-implies-nonuniqueness: that is Hutchcroft's conclusion p_c<p_u from an l2 hypothesis; this derives the four archive pivotal kernel estimates on graphs with p_c<p_(2->2).
  fpbs-pivotal-budget-universal: that asks for the budget on every nonamenable Cayley graph; this proves it, with a bounded count, only on graphs with p_c<p_(2->2).
  fpbs-pivotal-nonconcentration-universal: that asks for nonconcentration on every nonamenable Cayley graph; this proves B(epsilon)=0 only on graphs with p_c<p_(2->2).
  fpbs-integrated-sensitivity-universal: that asks for vanishing integrated sensitivity on every nonamenable Cayley graph; this proves it only on graphs with p_c<p_(2->2).
  fpbs-universal-subcritical-pivotal-growth-rate: that asks for the growth rate on every nonamenable Cayley graph; this proves rate zero only on graphs with p_c<p_(2->2).
---

Corollary 4.2 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`.

Let `G` be a nonamenable Cayley graph with `p_c(G)<p_(2->2)(G)`. Fix
`p0 in (p_c, p_(2->2))` and put `C_0 = 2d||T_(p0)||^2`, which is finite. Then
for both walks, all `n>=1`, all `R>=n` and all `p<=p0`,

    E_p[N_(n,R) | E_(n,R)] <= C_0.

So on `G` each kernel holds as stated on its node:

* `fpbs-pivotal-budget-universal`, with `C=C_0` and a count bounded
  independently of `n`;
* `fpbs-universal-subcritical-pivotal-growth-rate`, since
  `L_n(p0) <= C_0/n`;
* `fpbs-integrated-sensitivity-universal`;
* `fpbs-pivotal-nonconcentration-universal`, with `B(epsilon)=0` for
  `epsilon <= p0-p_c`.

This gives no new graph with `p_c<p_u`, because `p_(2->2) <= p_u`
(arXiv:1804.10191, TeX source line 301). Whether every nonamenable Cayley graph
satisfies the hypothesis is not addressed here; compare
`fpbs-nonamenability-bounds-critical-connectivity-operator`.
