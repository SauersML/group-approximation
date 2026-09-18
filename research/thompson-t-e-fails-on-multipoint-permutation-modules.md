---
rg: 2
id: thompson-t-e-fails-on-multipoint-permutation-modules
kind: claim
title: The one-word basis candidate E of Thompson's T fails in Z ≀_X T whenever some point stabilizer of the T-set X preserves a finite set of at least two circle points, so multipoint permutation modules give no witness
requires:
  - thompson-t-identities-one-word-basis-over-cantor-overgroups
distinct_from:
  thompson-t-identities-hold-in-circle-orbit-wreath-overgroups: that proves wreath products along orbits of single points satisfy every mixed identity of T; this proves wreath products along orbits of finite sets or tuples of two or more points violate E, so neither kind separates E from the other identities.
  thompson-t-identities-one-word-basis-over-cantor-overgroups: that builds the word E and the squeeze configuration inside homeomorphism groups; this reuses the configuration with an orientation-preserving element of T and reads the failure in the lamp coordinate by Fox calculus.
---

**ESTABLISHED** by the proof below. Lane proof by bh-ffwz-q59, 2026-09-18. It is not reviewed.

## Statement

Let `X` be a `T`-set containing a point `ξ` whose stabilizer is contained in the setwise
stabilizer `T_{S}` of a finite set `S ⊂ S^1` with `|S| ≥ 2`. Then `Z ≀_X T = Z[X] ⋊ T` does not
satisfy `E`. The same holds for every split extension `L ⋊ T` with `Z[X] ≤ L` as a `T`-module,
and for every overgroup of `T` containing such a group.

This covers orbits of ordered or unordered finite tuples of at least two points, orbits of
arcs (whose stabilizers fix the endpoints), and the regular `T`-set.

## Proof

**Reductions.**
- The `T`-map `xH ↦ x·S` onto the orbit `Ω_S = T·S` makes `Z[Ω_S]` a quotient module of `Z[X]`. So it
  suffices to treat `X = Ω_S`, the orbit of a finite set `S` with `m ≥ 2` points.
- **Fox calculus.** For `w ∈ T * ⟨x⟩` with `w|_T = 1`, and `(l, h) ∈ Z[X] ⋊ T`, we have
  `w(l, h) = (σ_w(h) l, 1)`, where `σ_w(h) ∈ Z[T]` is the Fox derivative `∂w/∂x` evaluated at
  `x = h`.

**The element h.** Use the arcs `A_i`, constants and transports `c, d` of `E`
(`thompson-t-identities-one-word-basis-proof`), and let `G_12` be the gap between `A_1` and `A_2`.
- **The rotation.** The cyclic order of `(A_2, A_1, G_12)` is positive. So some `g ∈ T` has
  `g(A_1) ⊆ A_2`, `g(A_2) ⊆ A_1` and `g(A_3) ⊆ G_12`, each compact in the interior of its target.
- **The adjustment.** Levels 1 and 2 of Step 3 of that proof apply verbatim to `h = u_1 u_2 g`, with
  `u_i ∈ T_(A_i)`. They make `P := [s_12, c s_21 c^{−1}](h) = Y ≠ 1`, supported in a small arc
  `O_1 ⊂ A_1`, where `O_1, aO_1, a^2O_1, a^3O_1` are pairwise disjoint.
- **The third commutator is trivial.** `β_3 = h a_3 h^{−1}` is supported in `g(A_3) ⊆ G_12`. That
  is disjoint from `A_3` and untouched by the `u_i`, so `s_33(h) = 1`.

**The Fox derivative.** With `Q = d s_33 d^{−1}`, so `Q(h) = 1`:
`σ_E(h) = (P − 1) · d · (a_3 − 1)(1 − β_3)`,
from `∂[P, Q] = (1 − PQP^{−1}) ∂P + (P − [P, Q]) ∂Q` and `∂s_33(h) = (a_3 − 1)(1 − β_3)`.

**A point where it does not vanish.** `T` is dense in `Homeo+(S^1)`, so the orbit `Ω_S` meets every
cyclically ordered product of open arcs. Choose `S = {p, q} ∪ R` in `Ω_S` with:
- `p ∈ supp β_3 ⊆ G_12`;
- `q ∈ d^{−1}(supp Y) ⊆ d^{−1}(O_1) ⊆ A_3`, so `z := dq` is moved by `Y`;
- `R` inside the gap `G_23`.

The cyclic order `p < R < q` matches `G_12 < G_23 < A_3`. Write `p' = β_3 p` and `q* = a_3 q`.
1. **Applying `1 − β_3`.** `β_3` moves only `p`, which gives `δ_S − δ_{S'}`, where `S'` replaces
   `p` by `p'`.
2. **Applying `a_3 − 1`.** `a_3` moves only `q`, which gives
   `δ_{p,q*,R} − δ_{p',q*,R} − δ_{p,q,R} + δ_{p',q,R}`.
3. **Applying `d`.** We have `d q* = a^3 z`, which lies in `a^3O_1` and so outside `O_1`. The images
   `dp`, `dp'` and `dR` lie outside `A_1 = d(A_3)`.
4. **Applying `Y − 1`.** `Y` fixes `dp`, `dp'`, `dR` and `a^3 z`, and it moves `z`. The terms
   containing `a^3 z` cancel, which leaves
   `−δ_{dp,Yz,dR} + δ_{dp,z,dR} + δ_{dp',Yz,dR} − δ_{dp',z,dR}`.
   These four sets are distinct: `Yz ∈ O_1` avoids the other points, and `Yz ≠ z`.

So `σ_E(h) δ_S ≠ 0`, and `E(δ_S, h) ≠ 1`. ∎

## Where the permutation-module case now stands

- **Point orbits satisfy every identity** (`thompson-t-identities-hold-in-circle-orbit-wreath-overgroups`).
- **Multipoint orbits violate E** (this node).
- **What is left.** A permutation-module witness against the basis `E` would need a `T`-set whose
  stabilizers preserve no finite set of two or more points and are not point stabilizers. Such
  stabilizers would be exotic subgroups of `T`.
- **Not done.** General non-permutation modules, amalgams and HNN extensions, and non-germ
  blow-ups.

## Lesson for general BH

For circle-type hosts, the one-word basis `E` separates lamps attached at points, which are
harmless, from lamps attached at configurations of two or more points, which violate `E` already.
The mechanism is that a rotation of `T` can swap two arcs and park the third in a gap. Then
`s_33 = 1` while the nested commutator `Y` survives, and Fox calculus reads `Y` off a lamp placed
on a two-point configuration. So among permutation modules, the identities of `T` are
all-or-nothing: they hold on point orbits and fail already at `E` on anything larger.
