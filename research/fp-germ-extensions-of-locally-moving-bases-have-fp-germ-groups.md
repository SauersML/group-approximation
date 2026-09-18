---
rg: 2
id: fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups
kind: claim
title: Over any finitely generated base that moves points locally and has finitely presented germ groups, a finitely presented finite-singularity extension has finitely presented germ groups at every point
distinct_from:
  fp-almost-v-groups-have-fp-germ-groups: that is the case B = V on the Cantor set; this proves the same localization for every finitely generated base group whose isotropy germ groups are finitely presented and which moves points locally, including V_(d,r), nV, F and T.
  shell-envelope-fp-forces-fp-germ-group: that is the shell case over V; this is base-independent.
  bhm-singfix-condition-forces-fp-germ-groups: that shows the one-point hypothesis of Belk--Hyde--Matucci Theorem 2.1 forces finitely presented germ groups; this shows finite presentation of the extension forces them, by any proof and over any such base.
---

**ESTABLISHED** by `fp-germ-extensions-locally-moving-bases-proof` (lane proof, elementary;
it is the proof of `fp-almost-v-groups-fp-germ-groups-proof` with the base axiomatized;
gq-referee-a PASS, `research/artifacts/gq-referee-a-fp-germ-extensions-of-locally-moving-bases-have-fp-germ-groups.md`,
0d5da4a8c, example fix applied; no novelty claimed). The id keeps the words "locally moving"
for stability; the hypothesis used is (B3) below.

## Setting

`X` is a Hausdorff space and `B <= Homeo(X)` a group. A homeomorphism `g` is **B-local at
`x`** if it agrees on a neighbourhood of `x` with some element of `B`; `sing(g)` is the set of
points where it is not. For a group `E` of homeomorphisms and `x in X`, `(E)_x` is the group of
germs at `x` of the elements of `E` that fix `x`.

**Hypotheses on the base.**
- (B1) `B` is finitely generated.
- (B2) `(B)_x` is finitely presented for every `x in X`.
- (B3) `B` **moves points locally**: for every `x in X`, every open `U ∋ x` and every finite
  `F ⊂ X`, some `c in B` supported in `U` has `c(x) ∉ F`. This is strictly stronger than being
  locally moving in the sense of Belk--Hyde--Matucci: it forbids global fixed points.

## Theorem

Let `B <= E <= Homeo(X)` with `sing(g)` finite for every `g in E`. If `E` is finitely
presented, then `(E)_p` is finitely presented for every `p in X`. Explicitly, `(E)_p` is a
quotient of a free product of finitely many groups `(B)_x` and a free group of finite rank by
the normal closure of finitely many elements, read off from the relators and the finitely many
places where a relator applies a generator at one of its singular points.

## Examples of bases (hand remarks)

- `V_(d,r)` on its Cantor space: germ groups trivial or infinite cyclic.
- Brin--Thompson `nV` on `C^n`: an element fixing `x` acts near `x` as one box map, so its
  germ is a product of coordinate germs and `(nV)_x` embeds in `Z^n`.
- Thompson's `T` on the circle: a germ at `x` fixing `x` is a pair of one-sided affine germs
  of slope a power of 2, so `(T)_x` embeds in `Z^2`. (B3) holds via elements of `F` supported on
  a small dyadic arc around `x`.
- Thompson's `F` on the open interval `X = (0,1)`, with the same germ computation. On `[0,1]`,
  (B3) fails at the endpoints, which every element of `F` fixes, so the germ groups `(E)_0` and
  `(E)_1` are not covered.
- More generally any finitely generated group satisfying (B3) whose isotropy germ groups are
  finitely generated abelian.

(B3) holds in all of these because the orbits are dense and small supports can move a point
off any finite set.

## Consequences

1. **The germ method is local.** For every base above, and in particular for the finite germ
   extensions of Belk--Hyde--Matucci over `V_(d,r)`, `nV` and `T`, a finitely presented
   host has finitely presented germ groups at all its singular points (over `F`, at all its
   interior singular points), whatever the proof of
   finite presentation. Any subgroup that is forced into germ groups (as rigid inputs are over
   `V`, `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group`) must sit inside a
   finitely presented germ group.
2. **Uncertifiable is unpresentable.** Hosts whose germ group at some point is not finitely
   presented are not finitely presented at all. Over `V` this covers the aperiodic Grigorchuk
   hosts (`fp-almost-v-groups-have-fp-germ-groups`, Consequence 2).

## Lesson for general BH

A finite-germ extension neither creates nor destroys finite presentation at a point: `E`
finitely presented implies every germ group finitely presented, over any tame base. So the germ
method for Boone--Higman is exactly a **one-point problem**. It must realize the input, or for
a rigid input the whole input, inside one finitely presented germ group `Q`, and then assemble
`Q` with the base (the `SingFix` step of Theorem 2.1). Everything the germ method can prove
about an input is already a statement about finitely presented overgroups `Q` of the input
containing the base's local dilation. The global geometry of the host is free. This tells
future hosts where the work is: in `Q`, not in the base.

## Scope

- Only (B1)--(B3) and finiteness of singular sets are used. No fullness, no condition on point
  stabilizers, no Cantor structure.
- The converse is not claimed: finitely presented germ groups do not make `E` finitely
  presented.
- Twisted Brin--Thompson groups `SV_G` and Rover--Nekrashevych groups are bases only when
  their germ groups are finitely presented. That depends on `G` and is not checked here.
