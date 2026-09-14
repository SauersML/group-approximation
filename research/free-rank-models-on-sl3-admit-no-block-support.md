---
rg: 2
id: free-rank-models-on-sl3-admit-no-block-support
kind: claim
title: A rank model of EL_3 with positive free content on SL_3(F_p) admits no block support of its unit root elements, and such models exist over simple rings with ring rank models
distinct_from:
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that kills models whose unit root elements are block supported; this shows that models with positive free content on SL_3(F_p) never meet that hypothesis, and that such models exist over a simple ring that has a ring rank model.
  monomial-rank-models-are-hamming-models: that excludes models within o(n) of monomial matrices on the whole group; this concerns models that are monomial only on the finite subgroup SL_3(F_p), in a basis of their own.
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**ESTABLISHED** (artifact Section 4e, Proposition 10 and Example 11; verification requested
from `gk-vf-linear`). Let `p` be a prime, `R` a unital `F_p`-algebra, `H_0 = SL_3(F_p)` inside
`EL_3(R)`, and `M = prod_omega M_(n_i)(k) / d_omega` with `char k = p`. Let
`sigma : EL_3(R) -> M^x` have representatives `sigma_i` that are honest representations on
`H_0`, each containing `k[H_0]^(m_i)` as a direct summand, with `m_i / n_i -> mu > 0` along
`omega`. Then

```text
rk( (sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1) )  >=  mu,
```

so no orthogonal idempotents `p_1, p_2, p_3` of `M` block-support the six unit root elements.
Block support would force this product into `p_2 M p_3 · p_1 M p_2 = 0`.

**Existence.** `S_inf = lim M_(p^k)(F_p)`, under `a -> a (x) I_p`, is simple and has a ring rank
model. The regular representations of the level groups `SL_(3 p^k)(F_p) = EL_3(M_(p^k)(F_p))`
form a separating rank model of `EL_3(S_inf)` whose restriction to `H_0` is free.

**Consequence.** Nontrivial rank models of `EL_3` over a simple ring can be free on
`SL_3(F_p)`, where the propagation theorems give nothing, even when the ring has a ring rank
model. A proof of `leavitt-el3-rank-models-over-finite-fields-are-trivial` must treat models
that are projective on finite subgroups, using the Leavitt structure rather than a
summand-level search for block support.
