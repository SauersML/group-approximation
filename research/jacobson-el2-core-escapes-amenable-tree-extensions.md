---
rg: 2
id: jacobson-el2-core-escapes-amenable-tree-extensions
kind: claim
title: No group containing the six-generator core of EL_2(J) embeds, even locally, in an amenable-by-(tree group with trivial edge and amenable vertex stabilizers), so Schafhauser amalgams cannot certify MF for H_mix, P22(J) or EL_n(J)
distinct_from:
  binary-jacobson-el2-is-lef: that proves EL_2(J) is LEF; this proves EL_2(J) is outside the amenable-tree class S, so LEF and S are incomparable and neither certificate reaches P22(J) or H_mix through the other.
  normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree: that excludes normal Kazhdan subgroups of groups with amenable-edge tree actions; this excludes a Kazhdan-free group, EL_2(J), from every subgroup of an amenable extension of a trivial-edge tree group, by opposite locally finite unipotents and a torus.
  free-kernel-tree-actions-embed-in-free-generalized-wreath: that embeds groups with a free normal subgroup acting on a tree; this is a non-embedding theorem for amenable normal subgroups and trivial edge stabilizers.
  amenable-implies-operator-mf: that is the amenable MF input; this bounds how far amenable inputs can be pushed by tree amalgamation toward the double parabolic.
---

ESTABLISHED (route `jacobson-el2-core-escapes-amenable-tree-extensions-proof`).
This is a class kill for the MF side of
[[property-t-free-jacobson-head-collapse]] (HC). It does not decide HC.

## Notation

* `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`, `I = span{S^a Q T^b}`.
* `sigma : J -> L = F_2[z, z^-1]` sends `S -> z` and `T -> z^-1`. It
  also denotes the induced map `GL_2(J) -> GL_2(L)`.
* The core is
  `E0 = < x_12(r), x_21(r) : r in {1, S, T} > <= EL_2(J)`.
* The class `S` consists of the groups `G` that have an amenable normal
  subgroup `N` such that `G/N` acts on a simplicial tree with these
  properties:
  * without inversions;
  * with trivial edge stabilizers;
  * with amenable vertex stabilizers.
* A group is *locally in `S`* if each of its finitely generated
  subgroups embeds in some member of `S`.

## Statement

**Theorem.** `E0` is not a subgroup of any group in `S`. Hence no group
containing `E0` is locally in `S`. This covers the following groups:

* `EL_n(J)` for every `n >= 2`;
* `W = M_2(J) semidirect EL_2(J)`;
* `P22(J) = M_2(J) semidirect (EL_2(J) x EL_2(J))`;
* `H_mix = M_2(J) semidirect (EL_2(J) x <x_34(1), x_43(S)>)`.

**Members of `S`.** The class `S` is closed under subgroups. It
contains the following groups:

* every amenable group, using the one-vertex tree;
* every free product of amenable groups, using the Bass–Serre tree with
  `N = 1`;
* every Schafhauser amalgam `G_1 *_N G_2`, where the `G_i` are amenable
  and `N` is normal in both. Here `N` is normal in the amalgam, and the
  quotient is `(G_1/N) * (G_2/N)`.

The last family is exactly the groups that Schafhauser
(arXiv:2306.02498, Theorem 1.3) proves MF. They include the w13 Borel
amalgams `B_n^+ *_{N_n} B_n^-`, which surject onto `EL_n(J)` and keep
the head. The class `S` is larger than the set of groups known to be
MF: amenable-by-free groups lie in `S`, and they are not known to be MF
in general. So the theorem excludes more than the certified groups.

## Consequence for the MF side of HC

MF is a local property. So a group is MF if each of its finitely
generated subgroups embeds in a group that is certified MF, for example
a Schafhauser amalgam. Two further facts were proved on the swarm branch
and are not yet on main:

* `P22(J)` is not LEF (w12, `p22-double-parabolic-is-not-lef`);
* permutation (Kerr–Nowak) certificates are dead (w11).

Two ways to certify MF are not based on finite models: amenability and
Schafhauser amalgams. By the theorem, neither can prove MF for `P22(J)`,
`H_mix` or `EL_n(J)`, even after closing under subgroups and directed
unions.

For `EL_n(J)` with `n >= 3` this also follows from property (T): an
infinite Kazhdan group has property FA, so it cannot lie in `S`. The new
content is twofold:

* The proof is Kazhdan-free.
* It covers `EL_2(J)`, `W`, `P22(J)` and `H_mix`. None of these is
  Kazhdan, because each surjects onto `SL_2(L)`, and `SL_2(L)` acts on
  its Bruhat–Tits tree without a fixed point.
The w13 amalgam `Lambda_n -> EL_n(J)` does not split on any finitely
generated subgroup containing `E0`, and no amenable repackaging of it
does either.

Notice that `H_mix = (W semidirect <a>) *_W (W semidirect <b>)` is itself
an amalgam over a common normal subgroup, with `W` LEF but not amenable.
So the precise missing tool is a Schafhauser theorem with non-amenable,
LEF factors. Either of two things would kill the P22 lane:

* an MF theorem for `N`-normal amalgams of LEF groups;
* such a theorem just for `W semidirect D_inf`.

HC itself needs a relation outside every group locally in `S`.

## Invariant and death step

The invariant is *opposite locally finite unipotents with a separating
torus*. Suppose `pi : G -> G/N` is the tree quotient.

* Each nontrivial locally finite subgroup fixes exactly one vertex,
  because edge stabilizers are trivial.
* So `pi` of the upper unipotent preimage fixes a vertex `v+`, and `pi`
  of the lower one fixes a vertex `v-`.
* A lift of `diag(z, z^-1)` normalizes both, so it fixes the geodesic
  `[v+, v-]`.

There are two cases, and each fails:

* If `v+ = v-`, all of `E0` is elliptic, so `E0` is amenable.
* If `v+ != v-`, the torus lies in `N`, and its commutators give an
  amenable subgroup with a ping-pong triple.

The ping-pong triple is `x_12(f), x_12(f'), x_21(g)` acting on the
projective line over `F_2((z^-1))`, which is paradoxical. Every attempt
to certify MF of these groups by embedding them into `S` dies at this
torus step.
