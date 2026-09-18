---
rg: 2
id: thompson-t-e-fails-on-closed-set-permutation-modules
kind: claim
title: The basis candidate E of Thompson's T fails in Z ≀_X T whenever a stabilizer of X preserves a closed subset of the circle other than the empty set, a point, or the whole circle, so Cantor sets and orbit closures give no witness
requires:
  - thompson-t-e-fails-on-multipoint-permutation-modules
distinct_from:
  thompson-t-e-fails-on-multipoint-permutation-modules: that treats stabilizers of finite sets of at least two points; this treats stabilizers of arbitrary closed sets, such as Cantor sets and orbit closures, by a local non-invariance argument in place of point bookkeeping.
  thompson-t-identities-hold-in-circle-orbit-wreath-overgroups: that is the point case, where every identity holds; this shows every larger closed configuration already violates E.
---

**ESTABLISHED** by the proof below. Lane proof by bh-ffwz-q59, 2026-09-18. It is not reviewed.

## Statement

Let `X` be a `T`-set, and suppose some stabilizer `T_ξ` is contained in the setwise stabilizer
`T_{Z}` of a closed set `Z ⊂ S^1` with `Z ∉ {∅, S^1}` and `Z` not a single point. Then
`Z ≀_X T` does not satisfy `E`. The same holds for any split extension `L ⋊ T` with `Z[X] ≤ L`.

## Proof

**Reductions.**
- As in `thompson-t-e-fails-on-multipoint-permutation-modules`, it suffices to take `X = T·Z`.
- If `∂Z` is finite, it has at least 2 points and `T_{Z}` preserves it, so that node applies.
  Assume from now on that `∂Z` is infinite.

**Setup.** Fix `h`, `P = Y` and `s_33(h) = 1` as in that node, and put:
- `a = a_3`, supported in `A_3`;
- `β = β_3`, supported in the gap `G_12`;
- `W = d^{−1} Y d`, supported in `O = d^{−1}(O_1) ⊂ supp a`, with `aO ∩ O = ∅`.

`β` commutes with `a` and with `W`. Conjugating the formula of that node by `d` gives
`σ_E(h) δ_S = d · (1 − β) u`, where `u = (W − 1)(a − 1) δ_S` for `S` in the orbit.

**The vanishing criterion.**
- **When `u ≠ 0`.** `u = δ_(WaS) − δ_(WS) − δ_(aS) + δ_S` is nonzero iff `aS ≠ S` and `W` moves
  `S` or `aS`.
- **When `(1 − β)u ≠ 0`.** `W` and `a` are supported in `A_3`, so all four terms of `u` agree with
  `S` on `G_12`. If `β(S ∩ G_12) ≠ S ∩ G_12`, then every term of `βu` differs from every term of
  `u` on `G_12`. So `βu ≠ u` whenever `u ≠ 0`.

So it suffices to find `S = tZ` with:
- **(i)** `β(S ∩ G_12) ≠ S ∩ G_12`;
- **(ii)** `aS ≠ S`;
- **(iii)** `WS ≠ S`.

**Local non-invariance lemma.**
- **Setting.** Let `g ∈ T` and let `J` be a component of `supp g`, an open arc on which `g` has no
  fixed point. Let `C` be closed with a boundary point in `J`.
- **Claim.** Some `v ∈ T_J` satisfies `g(vC ∩ J) ≠ vC ∩ J`.
- **Why.** Otherwise `C ∩ J` is invariant under every `v^{−1} g v` with `v ∈ T_J`. Their products
  with `g^{−1}` generate a subgroup of `T_J ≅ F` containing a nontrivial normal subgroup, hence
  `[T_J, T_J]`. Every `[F, F]`-orbit in `J` is dense, so a closed `[T_J, T_J]`-invariant subset of
  `J` is `∅` or `J`. That contradicts the boundary point.

**Placing Z.** Choose components `J_β ⊂ G_12` of `supp β` and `J_W ⊂ O` of `supp W`. Choose an arc
`J_a` in the component of `supp a` containing `O`, disjoint from `O ∪ aO ∪ a^{−1}O`.
- **One boundary point in each arc.** `T` sends any three points of the infinite set `∂Z`, in
  suitable cyclic order, into the three disjoint arcs `J_β`, `J_a` and `J_W`. So some `t` puts a
  boundary point of `tZ` in each.
- **Three independent adjustments.** Apply the lemma in each arc, with `v_β ∈ T_(J_β)`,
  `v_W ∈ T_(J_W)` and `v_a ∈ T_(J_a)`, for the maps `β`, `W` and `a`. These have disjoint supports,
  so they commute and the choices are independent. For `a` the witness is a pair `x, ax` inside
  `J_a`, away from `O`.
- **Result.** `S = v_β v_W v_a tZ` satisfies (i), (ii) and (iii). Hence `σ_E(h) δ_S ≠ 0`. ∎

## Where item 1 (permutation modules) stands

- **Satisfy everything:** stabilizers of single points.
- **Violate E:** stabilizers of finite sets of at least two points, and of closed sets other than
  `∅`, a point and `S^1`. This includes Cantor sets, orbit closures, arcs and their unions.
- **Left open:**
  - subgroups of a point stabilizer that preserve no other closed set, such as the germ-trivial
    stabilizer `T_p^0`;
  - subgroups acting minimally on `S^1` other than `T`.

  For `T_p^0`, the other orientation cases of `E` (`s_12 = 1`, with the supports of `a_1` and `β_2`
  adjacent at `p`) are the natural test. It was not run.

## Lesson for general BH

For circle-type hosts, every lamp attached to a closed configuration larger than a point violates
the basis word `E`.
- **Why.** The three commuting factors of the Fox derivative of `E` can each change the
  configuration at a different place, and local non-invariance can be forced with the host's own
  rigid stabilizers.
- **Where witnesses can still live.** A module witness can only use subgroups that see a single
  point, possibly with germ data, or no closed set at all.
