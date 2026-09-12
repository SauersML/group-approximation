---
rg: 2
id: fpbs-elementary-matrix-semidirect-fixed-price-one
kind: claim
title: Gaboriau's commensurated-chain criterion gives elementary groups over infinite rings, extended by ring automorphisms, fixed price one
distinct_from:
  fpbs-kazhdan-groups-have-cost-one: that is the Hutchcroft--Pete infimal cost one for every Kazhdan group, one cheap action; this is equality of cost across every free action for a class containing the Kun--Thom Theorem E groups, by a commuting root-subgroup chain.
  kun-thom-free-nonsofic-action: that establishes a free nonsofic action of the Kun--Thom group; this shows that action, like every other free action of the same group, has cost one, so cost does not detect soficity of actions there.
---

**ESTABLISHED; a direct application of Gaboriau's criterion, not a new theorem.**
Let `R` be a countably infinite commutative ring, let
`r >= 3`, and let `H` be a countable group acting on `R` by ring automorphisms,
hence on `EL_r(R)` entrywise. Then

```text
G = EL_r(R) semidirect H
```

has fixed price one: every essentially free p.m.p. action of `G` has cost one.
It follows from Gaboriau's Theorem 2.45: increasing unions through infinite
commensurations, from [Gab00, Lemme V.3] and in the spirit of Critere VI.24. The
theorem is imported by `fpbs-elementary-matrix-semidirect-fixed-price-one-citation`
and applied to the root-subgroup chain written out in
`fpbs-elementary-matrix-semidirect-fixed-price-one-proof`. The case `R = Z` with `H`
trivial is Gaboriau's `SL(n,Z)`, `n >= 3` (his Corollary 2.44).

**Instance.** Kun--Thom Theorem E takes `R = F_q[x_1^(+-1),...,x_d^(+-1)]` and
`H = SL_d(Z)` acting by monomial substitutions, with `r, d >= 3`. So the free,
strongly ergodic, nonsofic action of `kun-thom-free-nonsofic-action` has cost
one. So do the Bernoulli shift and the profinite actions of the same residually
finite Kazhdan group. For this group cost does not see soficity: compression
rigidity produces a nonsofic action but no second value of cost.

**Scope and credit.** The fixed price argument is Gaboriau's. The only content
here is the choice of chain and the observation that it covers the Kun--Thom
group. It gives nothing
for groups with no infinite amenable subgroup, such as large odd free Burnside
groups, which is where `fpbs-burnside-positive-upper-cost` lives. It also says
nothing about Benjamini--Schramm for these groups beyond what fixed price one
already gives.
