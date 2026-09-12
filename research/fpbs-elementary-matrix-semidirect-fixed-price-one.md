---
rg: 2
id: fpbs-elementary-matrix-semidirect-fixed-price-one
kind: claim
title: Elementary groups of rank at least three over an infinite ring, extended by ring automorphisms, have fixed price one
distinct_from:
  fpbs-kazhdan-groups-have-cost-one: that is the Hutchcroft--Pete infimal cost one for every Kazhdan group, one cheap action; this is equality of cost across every free action for a class containing the Kun--Thom Theorem E groups, by a commuting root-subgroup chain.
  kun-thom-free-nonsofic-action: that establishes a free nonsofic action of the Kun--Thom group; this shows that action, like every other free action of the same group, has cost one, so cost does not detect soficity of actions there.
---

**ESTABLISHED.** Let `R` be a countably infinite commutative ring, let
`r >= 3`, and let `H` be a countable group acting on `R` by ring automorphisms,
hence on `EL_r(R)` entrywise. Then

```text
G = EL_r(R) semidirect H
```

has fixed price one: every essentially free p.m.p. action of `G` has cost one.
The proof is the proof route `fpbs-elementary-matrix-semidirect-fixed-price-one-proof`.

**Instance.** Kun--Thom Theorem E takes `R = F_q[x_1^(+-1),...,x_d^(+-1)]` and
`H = SL_d(Z)` acting by monomial substitutions, with `r, d >= 3`. So the free,
strongly ergodic, nonsofic action of `kun-thom-free-nonsofic-action` has cost
one. So do the Bernoulli shift and the profinite actions of the same residually
finite Kazhdan group. For this group cost does not see soficity: compression
rigidity produces a nonsofic action but no second value of cost.

**Scope.** This is the commensurated-chain technique of Gaboriau's criterion
(Gaboriau 2000, Criteres VI.24), written out for these groups. It gives nothing
for groups with no infinite amenable subgroup, such as large odd free Burnside
groups, which is where `fpbs-burnside-positive-upper-cost` lives. It also says
nothing about Benjamini--Schramm for these groups beyond what fixed price one
already gives.
