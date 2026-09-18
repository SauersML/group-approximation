---
rg: 2
id: fpbs-l2-threshold-not-lsc-at-trees
kind: claim
title: Free products of amenable groups with Z/2 are uniformly nonamenable, have p_(2->2) at most p_c of the amenable factor, and converge to regular trees whose l2 threshold is strictly larger, so p_(2->2) and the l2 slack drop under local limits inside X_(k,eta)
distinct_from:
  fpbs-l2-gap-class-closed-under-local-limits: that proves the upper semicontinuity of the slack g_M = Gamma_M - p_c and closedness of U_(M,delta); this proves the converse fails, with explicit sizes, inside one uniformly nonamenable space X_(k,eta) and at a tree.
  fpbs-direct-limit-certificates-add-no-slack: that compares a limit with its covering approximants (kernels grow toward the limit) and calibrates with an amenable limit; this compares a nonamenable limit (a tree) with its quotients, all uniformly nonamenable, where local closeness loses a fixed fraction of the slack.
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that proves p_c < p_(2->2) on free products with union generating sets; this bounds p_(2->2) from above on free products with an amenable factor and says nothing against that gap.
  fpbs-uniform-l2-gap-short-relator-cylinders: that conjectures uniform constants on each cylinder {w = e}; this is a calibration on the cylinder w = s_k^2, and is consistent with that conjecture.
artifacts:
  - experiments/fpbs-involution-free-product-l2-drop-2026-09-17/check.py
---

**ESTABLISHED.** Route `fpbs-l2-threshold-not-lsc-at-trees-proof`.
Write `T_p` for the operator with kernel `tau_p(x,y) = P_p(x <-> y)` and
`p_(2->2)(G) = sup{p : ||T_p||_(2->2) < infinity}`.

**(A) Amenable factor.** Let `A` be an infinite amenable group with finite
symmetric generating set `S_A`, `|S_A| = D`, and let `G` be the Cayley graph of
`A * Z/2 = A * <c>` on `S_A ∪ {c}`. It is `(D+1)`-regular and simple.

1. Every finite nonempty vertex set `F` has `|∂_E F| >= |F|/2`. Hence
   `rho(G) <= sqrt(1 - 1/(4(D+1)^2))`, and `1 - rho(G) >= 1/(8(D+1)^2)`.
2. `p_(2->2)(G) <= p_c(A)`. In fact `||T^G_p|| = infinity` for every
   `p > p_c(A)`.

**(B) Drop at trees.** Fix `m >= 2` and put `k = m + 1`,
`eta_k = 1/(8(2k-1)^2)`. There are infinite amenable (virtually `Z^m`)
`m`-marked groups `A_n` such that the `k`-marked groups
`G_n = (A_n * Z/2; a_1, ..., a_m, c)` converge to
`(F_m * Z/2; a_1, ..., a_m, c)`, whose Cayley graph is the `(2k-1)`-regular
tree `T_(2k-1)`. All of them lie in `X_(k,eta_k)`, in the cylinder
`Z_(k,eta_k,s_k^2)`. And

```text
limsup_n p_(2->2)(G_n) <= lim_n p_c(A_n) = 1/(2k-3)
                        <  1/sqrt(2k-2) <= p_(2->2)(T_(2k-1)),
lim_n p_c(G_n) = p_c(T_(2k-1)) = 1/(2k-2).
```

For `k = 3` (`eta = 1/200`, the tree `T_5`):

```text
p_(2->2)(T_5) >= 1/2,   limsup p_(2->2)(G_n) <= 1/3,
slack(T_5) >= 1/4,      limsup slack(G_n) <= 1/12,
```

where `slack = p_(2->2) - p_c`.

**Consequences.**

* `p_(2->2)` and the slack are not lower semicontinuous on `X_(k,eta_k)`, not
  even at a tree. The upper semicontinuity of
  `fpbs-l2-gap-class-closed-under-local-limits` is the only direction.
* For `k = 3`, every `delta in (1/12, 1/4)` and every `M`: `T_5` lies in
  `U_(M',delta)` with `M' = ||T^(T_5)_(1/4+delta)|| < infinity`. But every
  neighbourhood of `T_5` in `Z_(3,1/200,s_3^2)` contains `G_n` with
  `||T^(G_n)_(p_c(G_n)+delta)|| = infinity`. So `T_5` is not an interior
  point of any `U_(M,delta)` with `delta > 1/12`.
* **Spectral radius jumps (`k >= 4`).** `liminf_n rho(G_n) >= (2k-3)/(2k-1)`,
  which exceeds `rho(T_(2k-1)) = 2 sqrt(2k-2)/(2k-1)`. So `rho` is
  discontinuous along a convergent sequence inside one `X_(k,eta)`.

**Killed class.** Consider proofs of an l2 gap, uniform or pointwise, on
`X_(k,eta)` or on one of its cylinders that certify `p_(2->2) >= q` (or a
slack `delta`) at a model group and then extend it to every marked group whose
`R`-ball agrees with the model's. Such proofs include openness of
`U_(M,delta)`, finite-subcover transplants, and ball-local certificates. At the
tree `T_(2k-1)` every such certificate is capped by

```text
q <= 1/(2k-3)
delta <= 1/((2k-3)(2k-2))
```

The model itself has `q = 1/sqrt(2k-2)` and slack
`1/sqrt(2k-2) - 1/(2k-2)`. So these proofs die at the neighbourhood step: the
local slack is of order `k^-2`, while the model slack is of order `k^(-1/2)`.
Spectral data of the model do not repair this, by the jump of `rho`.

**Not a counterexample.** Every `G_n` has `p_c < p_(2->2)` by
`fpbs-free-product-cayley-graphs-have-critical-l2-gap`. The upper bound
`slack(G_n) <= p_c(A_n) - p_c(G_n)` stays bounded away from `0`. The family is
consistent with `fpbs-uniform-l2-gap-short-relator-cylinders`.
