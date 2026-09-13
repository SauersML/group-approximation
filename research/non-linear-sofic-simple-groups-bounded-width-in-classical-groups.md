---
rg: 2
id: non-linear-sofic-simple-groups-bounded-width-in-classical-groups
kind: claim
title: A finitely presented simple group that is not linear sofic over the defining field has bounded relator width in classical groups of every rank
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that proves bounded relator width over symmetric, alternating, sporadic and bounded-rank Lie type groups; this is the remaining family, classical groups of unbounded rank, under a linear soficity hypothesis instead of a soficity hypothesis.
  simple-group-support-and-semisimple-rank-models-collapse: that proves the linear rank collapse relator rank >= delta_0 generator rank in GL; this asks for the projective form of that collapse together with a covering lemma, which are exactly what turn collapse into bounded conjugacy width.
---

**ESTABLISHED (unreviewed, 2026-09-13).** Let `G = <X | R>` be an infinite finitely presented simple
group and `q` a prime power. Suppose `G` is not linear sofic over `F_q`. Let `Q` be
a finite quasisimple classical group over `F_q` of any rank: `SL_n(q)`, `SU_n(q)`,
`Sp_(2n)(q)`, `Omega_n(q)` or their simple quotients. Then there is `K = K(G, q)` such that every
tuple `a in Q^X` has every generator in `Cons_K^Q(R(a))`.

The constant can be taken uniform over all powers of the characteristic `p` of `F_q`. Derivation:
`classical-width-from-finite-field-linear-sofic-dichotomy`. The stronger field-uniform statements are
`simple-group-psl-width-is-finite-field-linear-soficity` and
`simple-group-classical-width-finite-field-linear-soficity`. Their assembly over all finite simple groups
is `simple-group-width-over-all-finite-simple-groups`.

**Payoff.** For the binary Leavitt unit group (integrally acyclic by `binary-leavitt-unit-group-integrally-acyclic`, so `H_1 = H_2 = 0`), together
with `simple-group-relator-width-in-finite-simple-targets`: if `R^x` is not linear sofic over
`F_q`, it has no weak models in finite simple groups over `F_q` with any bi-invariant lengths.
If `leavitt-el3-rank-models-over-finite-fields-are-trivial` holds for every `q`, every weak model
of `R^x` must use non-simple finite groups. That is the room of Glebsky's extension proofs.

## History of the covering step

- **Linear collapse: established.** In `GL_n(F_q)`, `max_r rk(r(a) - 1) >= delta_0 max_x rk(a_x - 1)`
  (item 3 of `simple-group-support-and-semisimple-rank-models-collapse`, any characteristic).
- **Projective collapse: established.** Item 4 of
  `simple-group-support-and-semisimple-rank-models-collapse`: with
  `rho(g) = min_lambda rk(g - lambda)`, every tuple satisfies
  `max_r rho(r(a)) >= (delta_0/2) max_x rho(a_x)`. The proof is the linear collapse for the adjoint
  tuple. An earlier version of this node assumed a vanishing Schur multiplier to lift projective
  tuples; that assumption is not needed.
- **Covering lemma: resolved (lane `ex-weak-sofic-classical-covering`, 2026-09-13).** The three pieces
  this node listed as open were settled as follows.
  - *Commutator choice `rk([B, h]) >= c rk B`.*
    - Near-central case: displace the moved subspace `W` onto an orthogonal copy. Then `[r(a), y]` is
      `r(b)|_W (+) copy of r(b)^-1`, of rank exactly `2 rk B`.
    - Isometry groups: the displacement is a product of two conjugate swap involutions, so it lies in
      `I(V)'`.
    - Proportional case: a greedy hyperbolic subspace `Y` with `dim(Y + hY) >= (3/2) dim Y` and a Levi
      companion matrix give a seed of support `Theta(n)`.
  - *Determinant bookkeeping in `PSL_n`.* It is not needed. A fixed template writes each generator as
    commutators (double commutators for isometry groups) times relator conjugates, and scalars cancel
    in commutators. The earlier plan of matching scalars with a block `prod_r r^(n_r)` is superseded.
  - *Class bounds for `Sp`, `SU`, `Omega`.* The fixed space of an isometry `k` with
    `s = rk(k - 1) <= n/4` has a stabilizer of order at most
    `q_F^(s(s+1)/2 + rs + (n-s)(n-s+1)/2)`. A big-cell lower bound for `|Q_0|` then gives
    `|k^(Q_0)| >= q^(sn/2 - 3n - 4)/4`
    (`research/artifacts/classical-relator-width-part1-class-sizes-2026-09-13.md`).
- **What bounded chief length would add.** The template trick with conjugate pairs
  `(r, r^-1)` handles products and wreath products with coordinatewise good factors and abelian or
  bounded-solvable permuting groups. With unbounded chief length the constants multiply in the
  naive induction.
- **Correction (same lane, later).** An earlier version of this bullet listed `p`-groups of growing
  class as room. They are not: `perfect-group-relator-width-over-nilpotent-groups` bounds the width
  of a perfect group over every nilpotent group, of any class, by one fixed template. So the room is
  non-nilpotent finite groups of unbounded chief length outside the good simple classes, for example
  iterated wreath products with non-nilpotent tops. (Classical groups are no longer room; see above.)
