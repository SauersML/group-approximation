---
rg: 2
id: amenable-crossed-product-gl-normal-structure-is-standard
kind: claim
title: Over a simple crossed product LC(X,K) ⋊ Γ by an amenable group, every subgroup of GL_n normalized by E_n is central or contains E_n (n ≥ 3)
distinct_from:
  steinberg-elementary-groups-are-simple-mod-centre: that covers normal subgroups of EL_n over every minimal effective ample groupoid, via local annihilation; this is the GL_n-level sandwich for amenable crossed products, via Stepanov's Theorem 4.4 and a dimension count.
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that treats free minimal Z^d-subshifts with box towers; this holds for every amenable group, every field and every n ≥ 3, with no towers.
artifacts:
  - research/artifacts/sk-stable-rank-b-stepanov-route-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `K` be a field and `Γ` an amenable discrete group acting minimally and topologically
freely on a compact totally disconnected space `X`. Put `R = LC(X,K) ⋊ Γ` and let `n ≥ 3`. Then every subgroup
`H ≤ GL_n(R)` normalized by `E_n(R)` either lies in the centre `Z(R)^× I_n` of `GL_n(R)` or contains `E_n(R)`.

In particular `EL_n(R)/Z(EL_n(R))` is simple. When `X` is an infinite subshift over a finite alphabet, `Γ` is finitely
generated and `K` is finite, EJZ gives property (T) as well. This includes:
- infinite minimal `Z`-subshifts (the note's groups, every `q` and `n`);
- free minimal `Z^d`-subshifts;
- minimal free subshifts over any f.g. amenable group.

The proof is `-proof`. It uses no stable rank and no towers.
