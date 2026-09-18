---
rg: 2
id: rsg-z2-locally-trivial-along-rational-attraction
kind: claim
title: In a finite-nucleus rational similarity group, a free abelian group of rank at least two has a nontrivial element that is the identity near every point whose orbit under one of its elements accumulates at a rational point with finite orbit
distinct_from:
  finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs: that is the statement at the rational point itself; this transports it backwards along an orbit to arbitrary points, including points with free orbits, which is the form a free-product argument uses.
  z2-free-z-embeds-in-a-finite-nucleus-rsg: that is the open host-class question; this is the dynamical step that replaces the germ property of Thompson's V in a Bleak--Salazar-Díaz-type proof.
  z2-free-z-does-not-embed-in-thompson-v: that is the theorem for V, proved by revealing pairs; this is one ingredient of such a proof, valid in every finite-nucleus RSG.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed).

**Setting.** `G ≤ R_{Γ,E}` is a rational similarity group with finite nucleus
(Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224v3). `A ≤ G` is free abelian of rank
`r ≥ 2`.

**Statement.** Let `x ∈ E`, `a ∈ A`, and `n_k → ∞` with `a^{n_k} x → ω`, where `ω` is a
rational point whose `A`-orbit is finite. Then there is `1 ≠ g ∈ A` that is the
identity on a neighbourhood of `x`. In particular `g x = x`, so no neighbourhood of `x`
has pairwise disjoint `A`-translates, and `x` has nontrivial stabilizer in `A`.

The same `g` works for every such `x` with the same `ω` and the same `a`.

**Proof.**
1. Let `O = A ω`, which is finite, and let `A' ≤ A` be the pointwise stabilizer of `O`. It
   has finite index, so it is free abelian of rank `r`.
2. By `finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs` (item 2, applied to
   `A'` at the rational point `ω`), some `1 ≠ g ∈ A'` is the identity on an open
   neighbourhood `W` of `ω`.
3. For large `k`, `a^{n_k} x ∈ W`. Then `a^{-n_k}(W)` is an open neighbourhood of `x`.
   On it, `g = a^{-n_k} g a^{n_k}`, because `A` is abelian, and the right side is the
   identity there because `g` is the identity on `W`.
4. So `g` is the identity near `x`. □

**Where the hypothesis holds.**
- **Thompson's `V`.** By Brin's revealing pairs, as used by Bleak--Salazar-Díaz
  (arXiv:0911.0979, §2.3), every point that is not periodic for `a` has forward orbit
  converging to one of finitely many attracting periodic orbits, and these consist of
  rational points. This is recalled, not re-derived here. A commuting `b` permutes the
  finitely many attracting periodic points of `a`, so their `A`-orbits are finite.
- **General finite-nucleus RSGs.** Not known. The missing input is a dynamics theorem:
  forward orbits of wandering points of an element accumulate at rational periodic
  points. For Röver--Nekrashevych groups of finite-state self-similar groups,
  attracting fixed points of prefix-extending cycles are rational, because the
  sequence of states along the cycle is eventually periodic. The general statement is
  sketched in the artifact, not proved.

**Use.** In the Bleak--Salazar-Díaz proof that `Z^2 * Z` does not embed in `V`, the
important points `I(α)` of the `Z^2`-generators and the germ structure of `V` at them
drive an algorithm on revealing pairs (arXiv:0911.0979, §4.2). This claim is the part of
that mechanism that survives in every finite-nucleus RSG. See Attempt 2 of
`z2-free-z-embeds-in-a-finite-nucleus-rsg`.
