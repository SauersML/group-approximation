---
rg: 2
id: leavitt-unit-groups-have-fixed-price-one
kind: claim
title: The first nonsofic group has fixed price one, and so does EL_r over every countably infinite ring
distinct_from:
  fpbs-elementary-matrix-semidirect-fixed-price-one: that is Gaboriau's chain criterion for EL_r over countably infinite commutative rings extended by automorphisms, covering the residually finite Kun--Thom groups; this drops commutativity and so reaches the binary Leavitt unit group, which is simple, nonsofic and not residually finite.
  openai-leavitt-unit-nonsofic: that is nonsoficity of the same group; this computes its cost and first L2 Betti number, which do not see nonsoficity.
  fpbs-fixed-price-universal: that is Gaboriau's fixed price problem for every countably infinite group; this settles it for one new class that contains the first nonsofic group.
---

**Theorem.** Let `R` be a countably infinite associative unital ring and `r >= 3`. Every essentially free
p.m.p. action of `EL_r(R)` has cost one. In particular:

1. For every countable field `K`, the unit group `U_K = L_K(1,2)^x` of the binary Leavitt algebra has
   fixed price one. So does `U = L_(F_2)(1,2)^x`, the first nonsofic group
   (`openai-leavitt-unit-nonsofic`).
2. `beta_1^(2)(EL_r(R)) = 0`, and `beta_1^(2)(U_K) = 0`.

**Proof in one paragraph** (full write-up in `leavitt-unit-groups-have-fixed-price-one-proof`). The
Steinberg relation `[e_ij(a), e_kl(b)] = 1` for `j != k`, `i != l` holds over every ring, because
`E_ij E_kl = 0` and `E_kl E_ij = 0`. Commutativity of `R` is never used. So the six root subgroups of
`EL_3(R)` can be added one family at a time, each commuting with an infinite root subgroup already present,
starting from the infinite abelian group `E_12(R)`. Gaboriau's commensurated-chain theorem (Critères
VI.24(3), with Furman) gives cost at most that of `E_12(R)`, which is one. For `U_K`, the three-leaf prefix
code identifies `U_K` with `GL_3(R) = EL_3(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`). Gaboriau's
inequality `beta_1^(2) <= C - 1` (`fpbs-amen2-betti-cost-input`) gives item 2.

**What it says about approximation.**
- Cost, fixed price and `beta_1^(2)` do not distinguish the first nonsofic group from `SL_3(Z)`.
- The same holds for the Kun--Thom groups (`fpbs-elementary-matrix-semidirect-fixed-price-one`). It also
  holds for the Kun--Thom wreaths, which have an infinite amenable normal subgroup.
- So no orbit-equivalence invariant of cost type can certify soficity or nonsoficity of these groups. This
  matches `weak-invariants-give-no-bernoulli-rokhlin-lower-bound` on the entropy side.

**Scope and credit.** The chain argument is Gaboriau's (his `SL(n,Z)` case), with the Furman variant (3).
The only content here is that it needs no commutativity, so it covers the Leavitt unit groups. It gives
nothing about Benjamini--Schramm for these groups: fixed price one does not give `p_c < p_u`
(`fpbs-fixed-price-one-percolation-kernel` is a separate open claim). It gives no information on higher
`L^2`-Betti numbers of `U`.
