---
rg: 2
id: brin-thompson-first-return-maps-lie-in-kv-proof
kind: route
title: Bounded first-return maps are finite unions of compositions of brick maps
target: brin-thompson-first-return-maps-lie-in-kv
requires: []
---

Notation as in `rationals-embed-in-brin-thompson-group-2v-proof`: a *brick* is
`u_1C × ⋯ × u_kC`, and `kV` is the group of homeomorphisms of `C^k` that are
canonical (prefix replacement in each coordinate) on the pieces of a finite
brick partition.

**Item 1.**
- The sets `Y_r = Y ∩ T^-r Y \ (T^-1 Y ∪ ⋯ ∪ T^-(r-1) Y)` are clopen, because
  `T` is a homeomorphism and `Y` is clopen.
- By hypothesis, `Y` is their union for `1 <= r <= R+1`. So `r_Y` is locally
  constant and bounded.
- `T_Y` is continuous, since it equals `T^r` on `Y_r`.
- `T_Y` is injective. If `T_Y y = T_Y y'` with `y ∈ Y_r`, `y' ∈ Y_s` and
  `r <= s`, then `T^{s-r} y' = y ∈ Y`. Since `s - r < s`, the minimality of `s`
  forces `s = r`, and then `y = y'`.
- `T_Y` is surjective. For `z ∈ Y`, let `t >= 1` be least with `T^-t z ∈ Y`.
  It exists, because `T^-1 z` enters `Y` within `R` further backward steps: the
  hypothesis applied to `T^-(R+1) z` gives some `0 <= i <= R` with
  `T^{i-R-1} z ∈ Y`. Then `r_Y(T^-t z) = t` by minimality, so
  `T_Y(T^-t z) = z`.
- `Y` is compact, so `T_Y` is a homeomorphism.

**Item 2, brick-locality.** On `Y_r`, `T_Y = T^r` is a composition of `r` maps
that are canonical on finite brick partitions. Refining gives a finite brick
partition of `Y_r` on which `T^r` is canonical. So `T_Y` is canonical on a
finite brick partition of `Y`.

**Existence of ψ.**
- `Y` is compact and open, and bricks form a basis of clopen sets. So `Y` is
  a finite disjoint union of bricks `B_1, …, B_s`. Refine overlaps by splitting
  bricks.
- `C^k` has a partition into `s` bricks `D_1, …, D_s` for every `s >= 1`: split
  one brick along its first coordinate, `uC ↦ u0C ⊔ u1C`, `s - 1` times.
- Map `B_i` onto `D_i` by the prefix replacement
  `(u_1w_1, …, u_kw_k) ↦ (u'_1w_1, …, u'_kw_k)`, where `B_i = ∏ u_jC` and
  `D_i = ∏ u'_jC`. This defines `ψ`.

**Conjugate.** `ψ T_Y ψ^-1` is a homeomorphism of `C^k`. It is a composition of
three maps, each canonical on a finite brick partition of its domain, so after
refinement it is canonical on a finite brick partition of `C^k`. Hence it lies
in `kV`. This holds for any brick-local `ψ`. ∎
