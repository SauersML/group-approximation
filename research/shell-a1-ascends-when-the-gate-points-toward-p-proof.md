---
rg: 2
id: shell-a1-ascends-when-the-gate-points-toward-p-proof
kind: route
title: Choosing the rigid stabilizer level past the lifting defects makes t^-1 contract D, and D exhausts A_1^0
target: shell-a1-ascends-when-the-gate-points-toward-p
requires:
  - v-point-stabilizers-are-ascending-hnn-extensions-of-v
  - shell-fp-stabilizer-forces-fp-germ-group
artifacts:
  - research/artifacts/gq-bh-bh-free-07-classical-ledger.md
---

Notation as in the claim. All facts about `K_n` and `t` come from
`v-point-stabilizers-are-ascending-hnn-extensions-of-v`.

**Step 0. The splitting.** `A_1 -> Q` is onto with kernel `K`. `eta(tau) = 1`, so
`A_1 -> Q -> Z` is onto and splits by `t`. Hence `A_1 = A_1^0 ⋊ <t>`, where `A_1^0` is the
kernel of `A_1 -> Z`, which is the preimage of `Q^0`. The subgroup `A_1^0` contains `K`.

**Step 1. The lifting defects.** From `B <= tau B tau^-1` we get `tau^-1 B tau <= B`. So for each
`i` there is a word `w_i` with `tau^-1 b_i tau = w_i(b_1, ..., b_r)` in `Q`. In `A_1` this reads

    t^-1 b^_i t = w_i(b^) k_i

for some `k_i` in `K`. Only finitely many `k_i` occur. Choose `M >= 2` with every `k_i` in
`K_(M+1)`, which is possible because `K = union K_n` increases.

**Step 2. `t^-1` contracts `D`.** Put `D = <K_M, b^_1, ..., b^_r>`. It is finitely generated,
because `K_M` is a copy of `V`.
- `t^-1 K_M t = K_(M-1) <= K_M`.
- `t^-1 b^_i t = w_i(b^) (t^-1 k_i t)`, and `t^-1 k_i t` lies in `K_M` because `k_i` is in `K_(M+1)`.
So `t^-1 D t <= D`. Also `D <= A_1^0`, since `K_M <= K` and each `b^_i` lies over `B <= Q^0`.

**Step 3. Exhaustion.** Put `U = union_(n >= 0) t^n D t^-n`. It is a union of an
increasing sequence of subgroups, hence a subgroup, and `U <= A_1^0`.
- `U ⊇ union t^n K_M t^-n = union K_(M+n) = K`.
- The image of `U` in `Q` contains `union tau^n B tau^-n = Q^0`.
- Since `U` contains `K`, it is the full preimage of its image, so `U = A_1^0`.

**Step 4. The HNN structure.** By Steps 0 and 3, `A_1 = U ⋊ <t>` with
`U = union t^n D t^-n` and `t^-1 D t <= D`. The standard identification in the proof of
`v-point-stabilizers-are-ascending-hnn-extensions-of-v` (item 3) gives `A_1` isomorphic to
`D *_phi` with `phi(d) = t^-1 d t`. The map `phi` is injective because it is a conjugation.

**Step 5. Finiteness.** A presentation of `D` together with the relations
`t^-1 d_j t = phi(d_j)`, one for each generator `d_j` of `D`, presents `D *_phi`. So `D`
finitely presented implies `A_1` finitely presented. The type `F_n` version is the standard
one for ascending HNN extensions.

**Why (G−) fails.** Under (G−) one needs `t D t^-1 <= D`. But `t K_M t^-1 = K_(M+1)` is not
contained in `K_M`, so no `D` containing some `K_M` can be `t`-invariant. Dropping `K_M` loses
exhaustion of `K` unless the `b^_i` generate `K` by conjugation. That case is not treated.
