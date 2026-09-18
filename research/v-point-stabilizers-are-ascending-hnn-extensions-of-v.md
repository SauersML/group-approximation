---
rg: 2
id: v-point-stabilizers-are-ascending-hnn-extensions-of-v
kind: claim
title: The stabilizer in Thompson's V of the point 0^infinity is an ascending HNN extension of V
distinct_from:
  shell-fp-stabilizer-forces-fp-germ-group: that derives finite presentation of a germ group from finite presentation of a one-singularity shell stabilizer; this decomposes the nonsingular stabilizer Stab_V(0^infinity) itself.
artifacts:
  - research/artifacts/gq-bh-bh-free-07-classical-ledger.md
---

**ESTABLISHED** by `v-point-stabilizers-are-ascending-hnn-extensions-of-v-proof` (lane
proof, elementary; not independently reviewed; no priority claimed). Type `F_infinity`
of point stabilizers of `V` is Belk–Hyde–Matucci arXiv:2407.03149, Appendix A. The
decomposition below is a short direct route to it and is likely folklore.

Let `C = {0,1}^N`, `p = 0^infinity`, and for `n >= 1` let
`K_n = {v in V : v is the identity on 0^n C}`. Let `t in V` be

    t(0w) = 00w,   t(10w) = 01w,   t(11w) = 1w.

Then:
1. `K_n` is isomorphic to `V` for every `n >= 1`, and `K = union_n K_n` is the group of
   elements of `V` that are the identity near `p`.
2. `t` fixes `p`, its germ generates the germ group `(V)_p` (infinite cyclic), and
   `t K_n t^-1 = K_(n+1)` for `n >= 1`.
3. `Stab_V(p) = K ⋊ <t>`, and `Stab_V(p)` is isomorphic to the ascending HNN extension
   `K_2 *_phi` with `phi(k) = t^-1 k t`, an injective, non-surjective endomorphism of
   `K_2`, which is isomorphic to `V`.
4. Hence `Stab_V(p)` has type `F_infinity`.

**Why it matters here.** The universal shell route needs `A_1 = SingFix({p},{p})` to be
finitely presented. `A_1` is an extension of the same non-finitely-generated `K` by the
germ group `Q`. Items 2–3 are the mechanism that makes `K` harmless for `Q = <tau>`: the
germ letter `t` stretches each `K_n` onto `K_(n+1)`. The companion node
`shell-a1-ascends-when-the-gate-points-toward-p` extends this
mechanism to shell germ groups.
