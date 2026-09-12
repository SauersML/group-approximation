---
rg: 2
id: sl3-primary-mass-vanishes-by-kirillov-tightness
kind: route
title: Exact corner intertwiners give positive orbit covariance and prohibit escape to projective coadjoint infinity
target: sl3-primary-exact-congruence-mass-vanishes-at-every-prime
requires: []
artifacts:
  - research/artifacts/sl3-primary-exact-sector-kirillov-tightness-2026-09-08.md
  - research/artifacts/independent-kirillov-primary-sector-audit-2026-09-08.md
---

The first artifact gives the complete proof in finite tracial
coordinates; the second independently audits the orbit-method,
CRT, total-variation, compactification, and prime-two steps.

1. A fixed overlap Kazhdan estimate projects H_n to an exact
   intertwiner T_n with ||T_n-H_n||_2 ->0. Its polar supports have
   trace 1-o(1).
2. Simultaneous CRT lifts at p^(a_n+2) and modulo m_n make T_n
   intertwine the primary factors alone on the full compact
   parahoric K intersect h^-1 K h.
3. Exact positive orbit measures on a fixed Lie lattice are
   K-invariant. Restricting the common corner and its complements
   to a second fixed principal group gives total-variation
   covariance modulo a fixed compact annihilator. At two, take
   one further square restriction in both groups.
4. Fatten the additive-dual measures and compactify the vector
   space projectively. Any escaping mass is K- and h-invariant
   on the boundary. Recurrence forces it into the finite union
   of h-weight spaces, while Zariski density of K and coadjoint
   irreducibility prohibit an invariant support there.
5. The resulting tightness gives uniform normalized-2-norm
   continuity on deep congruence groups. Repeated fixed powers
   of h contract x_12(1) into them. First pass n to infinity,
   then the fixed power to infinity. Weyl conjugation and
   property T of C force the trace of the nontrivial primary
   projection to tend to zero.

The only external positive character formulas used are
[Boyarchenko--Sabitova](https://arxiv.org/pdf/math/0608126),
Theorems 2.6 and 2.8. No orbit formula on a nonuniform parahoric,
approximate BCH series, character-value-to-TV inference, or
conductor-only shift profile is used.
