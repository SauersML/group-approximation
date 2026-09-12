---
rg: 2
id: anti-central-k0-states-equal-lifted-trace-on-signed-thompson
kind: claim
title: Every K_0 state of the ternary anti-central summand equals the lifted trace on the finite subgroups of the signed Thompson group
distinct_from:
  anti-central-rank-models-see-haar-measure-on-signed-diagonal: that computes the rank law of an anti-central rank model on the clopen indicators of the signed diagonal; this forces every K_0 state, rank model or not, on all idempotent matrices over every finite subgroup of the signed Thompson group.
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

**ESTABLISHED** (proof: route `anti-central-k0-states-lifted-trace-proof`; verification requested from
`w4-vf-linear-b`, forwarded by `w3-vf-linear`).

Let `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `H = E x| V` the signed Thompson group, and `Gamma` any subgroup with
`H <= Gamma <= G`. Let `s` be a state on `(K_0(eps_- F_3[Gamma]), [eps_-])`. Then:

1. `s([1_U]) = lambda(U)` for every clopen `U` of the odd-measure space `M_-`, where `lambda` is Haar measure.
2. For every finite subgroup `K <= H` containing `z`, every `Gamma`-conjugate of it, and every idempotent matrix `p`
   over `eps_- F_3[K]`, `s([p]) = 2 dim_(F_3)(p F_3[K]^n) / |K|`, the lifted trace normalized at `eps_-`.

For `Gamma = G`, a state exists iff `ternary-anti-invariant-swap-corner-is-full` fails
(`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`). So an obstruction to the corner has no freedom on
the locally finite part of `H`. A solution must produce, through elements outside finite subgroups, a `K_0` relation
among finite-subgroup projectives of `H` that the lifted trace forbids, such as `[eps_-] <= [q_[0]]`.

**Where a state can see `h`.** The depth-one semidihedral group `<w, d, h>` of order sixteen is not conjugate into
`H`: every order-eight element of `H` with fourth power `z` is conjugate to its negative, and `hw` is not. Its
anti-central algebra is `M_2(F_3) x M_2(F_3)`, and the split `t` of a state between the evaluation block and the
twisted block is not determined by part 2. Whether `t = 1/2` for every state is open. Remark 2.3 of the artifact.
The transpose-inverse automorphism fixes `H` pointwise and exchanges the two blocks, so a state can always be averaged
to `t = 1/2` (`anti-central-k0-states-can-be-chosen-transpose-invariant`).
