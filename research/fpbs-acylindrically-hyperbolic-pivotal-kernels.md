---
rg: 2
id: fpbs-acylindrically-hyperbolic-pivotal-kernels
kind: claim
title: Cayley graphs of acylindrically hyperbolic groups satisfy all four pivotal kernels with bounded counts
distinct_from:
  fpbs-pivotal-budget-universal: that asks for the budget on every nonamenable Cayley graph; this proves it, with a bounded count, only on Cayley graphs of acylindrically hyperbolic groups, so products such as F_2 x Z stay open.
  fpbs-pivotal-kernels-hold-on-known-gap-test-graphs: that checks the kernels on trees, hyperbolic groups and tree-by-lattice products; this covers every Cayley graph of every acylindrically hyperbolic group, including non-hyperbolic ones.
  fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels: that proves the kernels under the hypothesis p_c<p_(2->2); this supplies the hypothesis and nonamenability for acylindrically hyperbolic groups and applies it.
  fpbs-sc-choi-seo: that imports p_c<p_u on the same graphs; this derives the four pivotal kernel estimates there, which gives no new case of p_c<p_u.
  fpbs-pivotal-nonconcentration-universal: that asks for nonconcentration on every nonamenable Cayley graph; this proves B(epsilon)=0 only on Cayley graphs of acylindrically hyperbolic groups.
  fpbs-integrated-sensitivity-universal: that asks for vanishing integrated sensitivity on every nonamenable Cayley graph; this proves it only on Cayley graphs of acylindrically hyperbolic groups.
  fpbs-universal-subcritical-pivotal-growth-rate: that asks for rate zero on every nonamenable Cayley graph; this proves it only on Cayley graphs of acylindrically hyperbolic groups.
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
---

Corollary B of `research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md`.

Let `G` be an acylindrically hyperbolic group and `S` a finite generating set.
Let `Gamma = Cay(G,S)`, of degree `d`, and use the setup of Section 1 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`. Fix
`p0 in (p_c(Gamma), p_(2->2)(Gamma))`, which is nonempty, and put
`C_0 = 2d||T_(p0)||_(2->2)^2 < infinity`. Then for both walks, all `n>=1`, all
`R>=n` and all `p<=p0`,

    E_p[N_(n,R) | E_(n,R)] <= C_0.

So on `Gamma` each kernel holds as stated on its node:

* `fpbs-pivotal-budget-universal`, with `C=C_0` and a count bounded
  independently of `n`;
* `fpbs-universal-subcritical-pivotal-growth-rate`;
* `fpbs-integrated-sensitivity-universal`;
* `fpbs-pivotal-nonconcentration-universal`, with `B(epsilon)=0` for
  `epsilon <= p0-p_c`.

This gives no new case of `p_c<p_u`, because Choi–Seo already prove it for these
graphs. The universal kernels stay open outside this class, for example on
arbitrary Cayley graphs of `F_2 x Z`.
