---
rg: 2
id: fpbs-kazhdan-cofinal-mod-p-growth-vanishes
kind: claim
title: In a Kazhdan group mod-p homology growth tends to zero along the profinite topology
distinct_from:
  fpbs-kazhdan-no-rapid-descent: that concerns abelian p-series and pro-p-cofinal families; this concerns families cofinal in the full profinite topology, whose members have arbitrary finite quotients, and needs the cocycle-support iteration rather than Theorem 1.15 as a black box.
  fpbs-kazhdan-positive-rank-gradient: that asks for d(Gamma_n) linear along some Farber chain; this proves d_p(Gamma_n) sublinear, for each fixed p, along every profinitely cofinal chain, which leaves d(Gamma_n) itself and non-cofinal chains open.
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

**ESTABLISHED (written deduction).** Let `Gamma` be a group with property (T),
`p` a prime and `c > 0`. Then there is a finite index subgroup `M` of
`Gamma` such that every finite index normal subgroup `N` contained in `M`
has `d_p(N) < c[Gamma:N]`.

Equivalently, no family of finite index normal subgroups with
`d_p(N) >= c[Gamma:N]` is cofinal in the profinite topology. In particular,
`d_p(Gamma_n)/[Gamma:Gamma_n] -> 0` along every nested normal chain whose
boundary action is the profinite completion.

Consequence for `fpbs-fixed-price-counterexample-exists`: a proof that the
profinite completion action of a Kazhdan group has cost above one cannot be a
fixed-prime abelianization count. It must use primes `p_n -> infinity`, or
non-abelian quotients of `Gamma_n`. A chain-based certificate at a fixed prime
must use a Farber chain that is not profinitely cofinal and is not an abelian
`p`-series with rapid descent.
