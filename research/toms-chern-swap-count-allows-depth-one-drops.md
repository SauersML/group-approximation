---
rg: 2
id: toms-chern-swap-count-allows-depth-one-drops
kind: claim
title: On one twisted swap family a Cuntz target of the swap pushforward of the leaf-average profile can have rank R - 1 or R everywhere, dropping by one on finitely many hyperplane slices, so Chern counts on a single swap family plus rank bands cannot give a trace-visible jump
artifacts:
  - experiments/toms-swap-drop-locus-2026-09-17/staggered_transport_model.py
  - experiments/toms-swap-drop-locus-2026-09-17/results.json
distinct_from:
  toms-swap-drop-locus-has-codimension-at-most-2m-plus-1: that proves every such target drops on a set of dimension at least 2j - 2m; this constructs targets whose drops have depth one on a set of dimension 2j - 2, which is sharp for that bound at m = 1 and shows no depth bound follows.
  toms-twisted-swap-pairs-are-totally-degeneracy-forcing: that shows a uniform contraction from one twisted half to the other vanishes somewhere; this uses exactly such vanishing sections, one coordinate at a time, so that each vanishing costs one rank on a hyperplane and nothing else.
  untwisted-doubling-tower-has-a-nonconstant-continuous-rank: that realizes the swap by a constant-rank rotation in the untwisted tower; this is the twisted replacement, which pays only depth-one drops.
  toms-simple-algebra-has-no-block-diagonal-rank-realizer: that gets its contradiction from a jump of K/2 top blocks at one point; this shows that the non-block-diagonal carries on one swap family need not produce any jump beyond one rank.
---

**Setting.** Let `j >= 1`, and let `L_1, L_2` be line bundles on `CP^j`, realized as
ranges of projections `gamma_1 in M_(n_1)(C(CP^j))` and `gamma_2 in M_(n_2)(C(CP^j))`. Let
`sigma` be a continuous section of `Hom(L_2, L_1)` with zero set `Z_sigma`. When `L_1 ⊗ L_2^*`
is `O(±1)`, as for Toms's twists `O(1), O(2)`, one can take `Z_sigma` to be a hyperplane.
Let `R >= 1`, `eta = 1/(8R)`, `t_i = (i - 1/2)/R + eta` and `c_i = 1 - (i - 1/2)/R`.

**Theorem (depth-one transport).** Let

```text
a'(s) = sum_i g_i(s) e_ii in M_R(C[0,1])_+,   g_i(s) = min(1, max(0, R (s - t_i))),
P(s)  = a'(s) tensor gamma_1 + a'(1 - s) tensor gamma_2   on  K = [0,1] x CP^j.
```

Then `rank a'(s) = #{i : t_i < s}`, which is within `1` of `R s`. `P` has ranks
`(p, q) = (0, R)` at `s = 0` and `(R, 0)` at `s = 1`. There is `Q in M_(R(n_1+n_2))(C(K))_+`
with `P <= Q`, such that

```text
rank Q in {R - 1, R}   everywhere,    {rank Q = R - 1} = {c_1, ..., c_R} x Z_sigma.
```

`P` is the slice form of `phi(a')` along a swap family `{(x(s), x(1-s))}` over an arc
carrying `h = s`, as in `toms-constant-rank-twisted-transport-costs-double-rank`.

**Obstruction (what it rules out).** Consider arguments that use only
- the structure of a containment target on one swap family (support bundles and
  their Chern classes away from the drop set, as in
  `toms-swap-drop-locus-has-codimension-at-most-2m-plus-1`), and
- the rank bands `m <= R'` and `rank >= R' - theta r_M` from point or branch traces on
  that family, with slack `theta r_M >= 1`.

No such argument can force a drop of depth `>= 2`, or a trace jump larger than
`1/r_M` in `A` (`beta_M / r_M` in `B`). In particular it cannot reproduce the
`delta/(2 r_n)` jump of the Poincare–Miranda firewall. The model meets all these
constraints with `R = R'`: the target has maximal rank `R'`, it never drops by more
than one, and its drop set has dimension `2j - 2 >= 2j - 2R'`. So combining the drop
count with the firewall along one swap family does not give the full obstruction in
`A`, nor in `B`. The brief's step is blocked at exactly this point.

**Model test.**
- *Consistent with the drop-locus bound.* `dim D = 2j - 2 >= 2j - 2m` with `m = R`.
  This is equality at `R = 1`.
- *Consistent with the constant-rank bound.* Constant rank would need `m >= 2R`. Here
  `m = R`, paid for by the drops.
- *Numerics.* The artifact checks `Q - P >= 0` up to `-7e-16`, `rank Q in {R-1, R}`,
  drops exactly at `c_i` on `{z_0 = 0}` and never off it, and the profile error
  `<= 0.625`, for `(j, R) = (2, 4)` and `(3, 3)`, with `L_1 = O(-2)`, `L_2 = O(-1)`.

**What it does not do.** The model lives on one swap family. It is not shown to extend
to a stage element on all of `X_M` whose ranks satisfy every trace band. The
strongest remaining route uses several sibling doubling nodes at once. Product
models then drop at a common point with depth equal to the number of nodes, which
is the kind of jump the firewall needs. The open case is coordinated transports that
stagger across nodes.

Proof: `toms-depth-one-drops-model-proof`. Internal derivation, unreviewed.
