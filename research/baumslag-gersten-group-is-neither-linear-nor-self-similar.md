---
rg: 2
id: baumslag-gersten-group-is-neither-linear-nor-self-similar
kind: claim
title: Every finite image of the Baumslag--Gersten group kills a, so the group is linear over no field and embeds in no rooted-tree automorphism group
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that proves every subgroup of a self-similar group is residually finite; this proves the Baumslag--Gersten group is not residually finite, so that obstruction applies to it, and adds that it is linear over no field.
  baumslag-gersten-base-is-elliptic-in-every-tree-action: that rules out tree hosts through ellipticity of the BS(1,2) base in actions on trees; this rules out linear and rooted-tree hosts through the finite quotients of the group.
artifacts:
  - research/artifacts/bh-baumslag-gersten-2026-09-12.md
---

**ESTABLISHED** (classical; self-contained proof, no novelty claimed).

Let `BG = < a, t | b a b^-1 = a^2 >` with `b = t a t^-1`, as in
`baumslag-gersten-base-is-elliptic-in-every-tree-action`.

1. **Finite images.** For every homomorphism `π` from `BG` to a finite group,
   `π(a) = 1`. So every finite quotient of `BG` factors through
   `BG / <<a>> ≅ Z` and is cyclic. This is Baumslag's 1969 theorem.
2. **Not residually finite.** `a ≠ 1` in `BG`, so `BG` is not residually
   finite.
3. **No linear host.** By Malcev's theorem, `BG` is linear over no field. So no
   theorem about linear groups, such as
   `positive-char-linear-groups-satisfy-boone-higman` or
   `char-zero-linear-groups-satisfy-boone-higman`, can certify `BG` or any
   group containing it.
4. **No rooted-tree host.** `BG` embeds in no `Aut(T)` for a locally finite
   rooted tree `T`, since level stabilizers show `Aut(T)` is residually finite.
   Hence it embeds in no self-similar group, and Zaremsky's finitely presented
   self-similar hosts (arXiv:2405.09722, Theorem 1.1) cannot contain it.

The proof is `baumslag-gersten-neither-linear-nor-self-similar-proof`. The host
map for `BG` is in `research/artifacts/bh-baumslag-gersten-2026-09-12.md`.
