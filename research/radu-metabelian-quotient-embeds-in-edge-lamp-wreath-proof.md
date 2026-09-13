---
rg: 2
id: radu-metabelian-quotient-embeds-in-edge-lamp-wreath-proof
kind: route
title: Project geodesics of the vertical tree to 1-chains of the Cayley graph of PGL_2(Z), apply Hurewicz, and read the edge orbits off the horizontal automaton
target: radu-metabelian-quotient-embeds-in-edge-lamp-wreath
requires:
  - radu-horizontal-tree-group-is-linear
  - radu-horizontal-quotient-is-arithmetic-lattice
  - gkp-wreath-permanence-theorem
artifacts:
  - research/artifacts/radu-edge-lamp-host-and-square-firewall-2026-09-13.md
---

# Proof

Full details are in the artifact, Sections 0–2.

**Item 1.**
* *Cocycle.* `T_v` is a tree, so `Z_1(T_v) = 0`, and two 1-chains with the same boundary are equal.
  So `[o, gh·o] = [o, g·o] + g_*[o, h·o]`. The quotient `π` is equivariant along `Γ_R → Q`, which
  gives `d(gh) = d(g) + ḡ·d(h)`, and `g ↦ (d(g), ḡ)` is a homomorphism.
* *Kernel.* If `ḡ = 1` then `g ∈ Λ_v`, and `d(g)` is the 1-cycle of the loop `g` in `Y`, i.e. its
  Hurewicz image in `H_1(Y) = Z_1(Y)`, since `Y` is a graph. The kernel of Hurewicz is
  `[Λ_v, Λ_v]`, because `Λ_v = π_1(Y)` is free and acts freely without inversions
  (`radu-horizontal-tree-group-is-linear`, item 3).
* *Edge orbits.* `A = <a,b,c>` acts on `T_v` through the automaton
  `a: x→x(a), y→y(a), z→z(b)`, `b: x→x(b), y→y(c), z→z(a)`, `c: x→z(c), y→y(b), z→x(c)`,
  which is read off the six relators. Elements of `W = V/Λ_v` act by left multiplication.
  - Labels are preserved up to `x ↔ z`.
  - `W` is simply transitive on the vertices of `Y`, and `Stab_Q(o) = C`.
  - On the link of `o`, `a` and `b` fix `xo, yo, zo`, while `c` swaps `xo ↔ zo`.
  - So the oriented `y`-edges form the orbit `Q/C`, with base `(o → yo)`, and the oriented
    `{x,z}`-edges form the orbit `Q/C_χ`, with base `(o → xo)`.
* *Host.* `e ↦ e − ē` embeds `C_1(Y)` equivariantly in `Z[E^or]`. Pulling back along
  `Q/C_χ → Q/C` embeds `Z[Q/C]` in `Z[Q/C_χ]`.

**Item 2.**
* *`D_4`.* In `Q`, `x` and `z` are distinct commuting involutions, and `cxc = z`, so
  `D_4 = <x,z> ⋊ <c>` has order 8. `D_4 ∩ C_χ = 1`, since `W ∩ C = 1` (`Γ_R = V·A` uniquely and
  `Λ_v ⊂ V`) and `c ∉ C_χ`.
* *Normalizing.* `c` normalizes `C_χ`, which has index 2 in `C`. For `x`: `xax = a`, `xbx = b`, and
  `xc = cz`, `zaz = b` give `x(cac)x = cbc` and `x(cbc)x = cac`.
* *The square.* The geodesic of `xzxz` from `o` projects to the 4-cycle `1 → x → xz → z → 1`.
  Its oriented edges are `e_0, xc·e_0, xz·e_0, zc·e_0`, and the reversed edges are
  `x·e_0, xzc·e_0, z·e_0, c·e_0`. The eight cosets `gC_χ`, `g ∈ D_4`, are distinct.

**Item 3.** Gao–Kunnawalkam Elayavalli–Patchell Theorem 3.6 (`gkp-wreath-permanence-theorem`):
`G` sofic, `H` sofic, `α` sofic imply `G wr_α H` sofic. Here `G = Z^2`, `H = Q`, which is linear
and hence residually finite, and `α` is `Q ↷ Q/C_χ`. Then pass to the subgroup `G_2`. ∎
