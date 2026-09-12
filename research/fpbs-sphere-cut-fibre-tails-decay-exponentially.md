---
rg: 2
id: fpbs-sphere-cut-fibre-tails-decay-exponentially
kind: claim
title: A sphere-restricted critical fibre operator of norm below one forces exponential decay of critical fibre tails
distinct_from:
  fpbs-tree-projected-sphere-bubble-l2-equivalence: that uses single fibres as cut sets and submultiplicativity of sphere bubbles on tree-projected generating sets; this uses fibre-saturated spheres, which separate every Cayley graph over every quotient, and needs an operator-norm bound at one radius instead of a sphere bubble below one.
  fpbs-rd-quotient-weighted-bubble-gives-critical-l2: that derives critical L2 boundedness from a weighted critical fibre bubble; this derives exponential decay of critical fibre tails, hence every polynomially weighted bubble, from one finite-radius operator norm and uses no property of the quotient.
artifacts:
  - research/artifacts/fpbs/docs/sphere-cut-fibre-bootstrap.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `S` a finite symmetric
generating set, `H` any normal subgroup, and `Q = Gamma/H` with word length `|.|`
from `pi(S)`. Put `sigma_p(q) = E_p|K_o ∩ Gamma_q|`, `sigma_{p,R} = sigma_p 1_{S_Q(R)}`
and `T_m(p) = sum_{|q| >= m} sigma_p(q)^2`, and let `lambda` be the left regular
representation of `Q`.

1. **Tail inequality.** For `p < p_c` and all `R, m >= 0`,

   ```text
   T_{R+m}(p)  <=  ||lambda(sigma_{p,R})||_{2->2}^2  T_m(p).
   ```

2. **Bootstrap.** If `theta = ||lambda(sigma_{p_c,R_0})||_{2->2}^2 < 1` for some
   `R_0 >= 1`, then for some `M < infinity`

   ```text
   T_m(p_c) <= M theta^(floor(m/R_0))  for all m,     and
   sum_q (1+|q|)^s sigma_{p_c}(q)^2 < infinity  for every s >= 0.
   ```

The cut is the fibre saturation `pi^(-1)(S_Q(R))` of a sphere. Every path from
`o` to a fibre at radius at least `R` crosses it. BK at the first crossing gives
`sigma_p(q) <= (lambda(sigma_{p,R}) sigma_p 1_{|.| >= |q|-R})(q)`.

**Necessary rate.** Under part 2, `theta^(1/R_0) >= e^(-h(Q))`, where `h` is the
volume entropy. Otherwise `chi_{p_c}` would be finite. So the hypothesis never holds
over quotients of subexponential growth. Proof: artifact Sections 1–2.
