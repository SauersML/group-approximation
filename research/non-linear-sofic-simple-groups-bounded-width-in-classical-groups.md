---
rg: 2
id: non-linear-sofic-simple-groups-bounded-width-in-classical-groups
kind: claim
title: A finitely presented simple group that is not linear sofic over the defining field has bounded relator width in classical groups of every rank
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that proves bounded relator width over symmetric, alternating, sporadic and bounded-rank Lie type groups; this is the remaining family, classical groups of unbounded rank, under a linear soficity hypothesis instead of a soficity hypothesis.
  simple-group-support-and-semisimple-rank-models-collapse: that proves the linear rank collapse relator rank >= delta_0 generator rank in GL; this asks for the projective form of that collapse together with a covering lemma, which are exactly what turn collapse into bounded conjugacy width.
---

**OPEN.** Let `G = <X | R>` be an infinite finitely presented simple group and `q` a prime
power. Suppose `G` is not linear sofic over `F_q`. Let `Q` be
a finite quasisimple classical group over `F_q` of any rank: `SL_n(q)`, `SU_n(q)`,
`Sp_(2n)(q)`, `Omega_n(q)` or their simple quotients. Then there is `K = K(G, q)` such that every
tuple `a in Q^X` has every generator in `Cons_K^Q(R(a))`.

**Payoff.** For the binary Leavitt unit group (integrally acyclic by `binary-leavitt-unit-group-integrally-acyclic`, so `H_1 = H_2 = 0`), together
with `simple-group-relator-width-in-finite-simple-targets`: if `R^x` is not linear sofic over
`F_q`, it has no weak models in finite simple groups over `F_q` with any bi-invariant lengths.
If `leavitt-el3-rank-models-over-finite-fields-are-trivial` holds for every `q`, every weak model
of `R^x` must use non-simple finite groups. That is the room of Glebsky's extension proofs.

## Attempts

- **Linear collapse: established.** In `GL_n(F_q)`, `max_r rk(r(a) - 1) >= delta_0 max_x rk(a_x - 1)`
  (item 3 of `simple-group-support-and-semisimple-rank-models-collapse`, any characteristic).
- **Projective collapse: established.** Item 4 of
  `simple-group-support-and-semisimple-rank-models-collapse`: with
  `rho(g) = min_lambda rk(g - lambda)`, every tuple satisfies
  `max_r rho(r(a)) >= (delta_0/2) max_x rho(a_x)`. The proof is the linear collapse for the adjoint
  tuple. An earlier version of this node assumed a vanishing Schur multiplier to lift projective
  tuples; that assumption is not needed.
- **Covering lemma: missing step.**
  - *Localize the generator.* An element `g` with `rk(g - 1) = m` preserves a decomposition
    `V = W (+) W'` with `dim W <= 2m` and `g|_(W') = 1`. Take `W = im(g - 1) + C`, with `C` a
    complement of `ker(g - 1)`.
  - *Localize the relator.* Let `h` be a relator value at rank distance `rho >= delta_0 m` from the
    scalars. A near-scalar `h` has `rk(h - 1)` of order `n` and would force a large subspace. So first
    remove the scalar part with a product `h (h^-1)^g` of two conjugates, which has rank at most
    `2 rho`. Choosing `g` so that this product keeps rank of order `rho` is part of the missing step.
    The product can then be conjugated into `SL(W'') x 1` for some `W'' ⊇ W` with
    `dim W'' <= 4 max(m, 2 rho)`.
  - *Cover.* By `liebeck-shalev-normal-subset-covering`, the class of `h` in `SL(W'')` covers
    `SL(W'')` in `c log|SL(W'')| / log|class|` steps.
  - *The class bound is elementary for `GL` and `SL`.*
    - The centralizer of `h` in `GL_d(q)` is the unit group of the centralizer algebra, so
      `|C_(GL_d(q))(h)| <= q^(dim C(h)) <= q^(d max(d - rho, d/2))`, by the Jordan-type count in the
      proof of item 4 of the collapse theorem.
    - So the `GL_d(q)`-class has size at least `c_0 q^(d min(rho, d/2))`, with
      `c_0 = prod_i (1 - q^-i) > 1/4`.
    - The `SL_d(q)`-class is at least that divided by `q - 1`.
    - With `d <= C rho`, the covering number is bounded.
  - *Scalar parts.* For near-scalar values `g = lambda (1 + B)` with small `rk B`, the closest scalar is
    approximately multiplicative on bounded words. By perfection, generator scalars are fixed products
    of relator scalars. So a first block `prod_r r^(n_r)` matches scalars, and the commutators
    `[r, h] = (1+B) h (1+B)^-1 h^-1` carry the local parts.
  - *What is open.*
    - A choice of `h` with `rk([B, h]) >= c rk B`.
    - The determinant bookkeeping in `PSL_n` when the scalar of a generator is not an `n`-th root of
      unity.
    - The analogous class bounds and localizations inside nondegenerate subspaces for `Sp`, `SU`
      and `Omega`.
- **What bounded chief length would add.** The template trick with conjugate pairs
  `(r, r^-1)` handles products and wreath products with coordinatewise good factors and abelian or
  bounded-solvable permuting groups. With unbounded chief length the constants multiply in the
  naive induction.
- **Correction (same lane, later).** An earlier version of this bullet listed `p`-groups of growing
  class as room. They are not: `perfect-group-relator-width-over-nilpotent-groups` bounds the width
  of a perfect group over every nilpotent group, of any class, by one fixed template. So the room is
  non-nilpotent finite groups of unbounded chief length outside the good simple classes, for example
  iterated wreath products with non-nilpotent tops, and classical groups until this claim is proved.
