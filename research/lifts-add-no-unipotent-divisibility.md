---
rg: 2
id: lifts-add-no-unipotent-divisibility
kind: claim
title: A central or covering lift of a group without (Q,+) contains none of GL_n(Q), SL_n(Q), PGL_n(Q), PSL_n(Q), Aff(Q), B_2(Q), U_3(Q)
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this rules out one family of routes to it, the T-bar-style lifts, and says where their divisibility would have to come from.
  q-free-lifts-reach-only-lattice-affine-q-groups: that allows every finite normal series with Q-free or central factors and excludes Aff(Q), B_2(Q) and the linear groups there, but not U_3(Q); this fixes the three-step shape Q-free, central, Q-free, which also excludes U_3(Q).
artifacts:
  - research/artifacts/gq-referee-b-lifts-add-no-unipotent-divisibility.md
---

**ESTABLISHED** through `lifts-add-no-unipotent-divisibility-proof`. Referee
PASS with no amendments (gq-referee-b, citation and hypothesis lens:
`research/artifacts/gq-referee-b-lifts-add-no-unipotent-divisibility.md`). The argument is elementary and no priority is claimed.

## Statement

Let `E` be a group with normal subgroups `N <= K` such that

- `N` contains no subgroup isomorphic to `(Q,+)`,
- `K/N` is central in `E/N`, and
- `E/K` contains no subgroup isomorphic to `(Q,+)`.

Then no group that contains one of the following embeds in `E`:
`GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)`, `PSL_n(Q)` for `n >= 2`,
`Aff(Q) = Q x| Q^x`, the Borel group `B_2(Q)`, and the Heisenberg group
`U_3(Q)`.

More precisely, if one of these groups `H` embeds in a group `E` with
normal subgroups `N <= K` as above except for the last condition, then its
elementary unipotent (or translation) subgroup `D ~ (Q,+)` embeds in `E/K`.

## Special cases

- **Central lifts** (`N = 1`, `K` central). Let `Gamma <= Homeo_+(S^1)` contain
  no copy of `(Q,+)`, and let `Gamma~ <= Homeo_Z(R)` be the group of all lifts
  of elements of `Gamma` to the universal cover. The lifts of the identity are
  the integer translations, which are central, and `Gamma~/Z ~ Gamma`. So
  `Gamma~` contains none of the groups above. For `Gamma = T` this is
  Ghys--Sergiescu's `T-bar`: `T <= V`, and `V` contains no copy of `Q`
  (Higman; survey arXiv:2306.16356v3, Theorem 4.4, "In particular, Q does not
  embed into V").
- **Covering lifts** (`N = K = Delta`). If `Delta` is the deck group of a
  regular covering, contains no `(Q,+)`, and is normal in a group `E` of
  homeomorphisms of the cover, then `E` can contain one of the groups above only
  if `E/Delta`, the group induced on the base, contains `(Q,+)`. For the tori
  `R^n -> T^n` the deck group is `Z^n`.

## Consequence for the root

The Belk--Hyde--Matucci device `Q <= T-bar` gets its divisibility from
rotation-type torsion of `T`, absorbed into the central `Z` of the lift. For
`H = (Q,+)` this is consistent, because every nontrivial subgroup of `Q` meets
the centre of `Q`. For `GL_n(Q)`, `SL_n(Q)`, `Aff(Q)` and `U_3(Q)` the
unipotent `(Q,+)` meets the centre of every Q-free quotient trivially. So no
lift, central or through a covering with Q-free deck group, supplies its
divisibility: the base group must already contain `(Q,+)`, and the question is
back on the base (circle-level, torus-level) group.

This is independent of the distortion obstruction O4 of
`gl-n-q-embeds-in-fp-simple-group`. O4 only concerns subgroups of `VA`. The
present claim covers lifts of every Q-free group, with or without distorted
elements.

Covers whose deck group contains `Q` are not covered. An example is the adelic
presentation of the solenoid, `(R x A_f)/Q`.

**Scope.** The three-step shape matters for `U_3(Q)`: it has a normal series with
factors `Z`, `Q/Z`, `Z^2`, `(Q/Z)^2`, all Q-free, so iterated towers of covers
and central extensions can contain it. For towers of any length, the exclusions
that survive are those of `q-free-lifts-reach-only-lattice-affine-q-groups`.
