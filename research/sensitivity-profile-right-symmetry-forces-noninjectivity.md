---
rg: 2
id: sensitivity-profile-right-symmetry-forces-noninjectivity
kind: claim
title: A cellular automaton whose single-site sensitivity profile has a nontrivial right symmetry is not injective
distinct_from:
  right-symmetric-sensitivity-profile-admits-no-decoder: that excludes left inverses under a right symmetry of order divisible by the alphabet size, by a decoder count; this excludes injectivity itself under a right symmetry of any nontrivial element, with no decoder and no order condition.
artifacts:
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be a group, `A = Z/n`, and `tau(x)(g) = f((x(gm))_(m in M))`. Fix `b != 0` and
put `p_b(m) = f(b e_m) - f(0)` for `m in M` and `p_b = 0` off `M`. If `p_b(mc) = p_b(m)`
for all `m`, for some `c != 1`, then `tau` is not injective.

*Why.* `tau(b e_k)(g) = f(0) + p_b(g^-1 k)`, so right invariance of `p_b` under `c` gives
`tau(b e_(kc)) = tau(b e_k)` while `b e_(kc) != b e_k`.

**Consequence.** Over `F_2`, `p_1` is the linear support `supp a` of the rule's algebraic
normal form. An encoder whose linear support is right-invariant under any nontrivial element
is not injective. This includes invariant-output encoders with linear part `k + hk`, with
`c = k^-1 h k`.
