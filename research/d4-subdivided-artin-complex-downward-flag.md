---
rg: 2
id: d4-subdivided-artin-complex-downward-flag
kind: claim
title: "Huang: the subdivision of the D_4 Artin complex along two leaf types is a bowtie-free downward flag poset"
distinct_from:
  h4-deligne-complex-upward-flag-toward-5-edge: that is upward flagness of the unsubdivided H_4 complex along a path order, which is open; this is downward flagness of the subdivided D_4 complex, which is proved.
  huang-relative-artin-complex-structure-lemmas: that collects the structural facts about relative Artin complexes along paths; this is a flagness theorem for a subdivided complex on a branched diagram.
---

Let `Λ` be the Coxeter diagram of type `D_4`: a centre `d` joined by edges labelled 3 to three
leaves `a, b, c`. Let `Δ = Δ_Λ` be its Artin complex.

**The `(a, b)`-subdivision.** Subdivide every edge of `Δ` between a vertex of type `â` and a
vertex of type `b̂`. The new midpoint vertices get type `m`. Cut each top simplex into two along
the codimension-1 face spanned by the vertices of types `m, d̂, ĉ`. This gives a complex `Δ'`.

Define `t` on the vertices of `Δ'` by `t = 1` on types `â, b̂`, `t = 2` on `m`, `t = 3` on `d̂`
and `t = 4` on `ĉ`. For vertices `x, y` of `Δ'`, let `x < y` when `x, y` are adjacent in `Δ'`
and `t(x) < t(y)`.

Then `<` is a partial order on the vertices of `Δ'`, and this poset is bowtie free and downward
flag: any three pairwise lower-bounded vertices have a common lower bound.

Literature import through `d4-subdivided-artin-complex-downward-flag-citation`.
