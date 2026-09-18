---
rg: 2
id: attracting-fixed-point-centralizers-embed-in-germ-groups
kind: claim
title: The centralizer of a homeomorphism with an attracting fixed point of dense basin embeds in the germ group at that point; in 2V a diagonal north-south flow z^p x z^q with pq != 0 has centralizer exactly Z^2
distinct_from:
  rational-germ-groups-of-germ-extensions-of-v-embed-in-2v: that classifies germ groups at rational points of germ extensions of V; this turns germ groups into bounds on centralizers, for any group of homeomorphisms.
  fiber-detecting-block-characters-force-npc-graph-manifolds: that excludes local product hosts for charged graph manifolds; this excludes the diagonal-fiber design in 2V, where a Seifert fiber is a diagonal flow, because such a flow commutes with no free group.
  finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs: that bounds abelian point stabilizers through germs in finite-nucleus RSGs; this bounds centralizers through germs, in any homeomorphism group.
artifacts:
  - research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md
---

**ESTABLISHED** (lane proof, elementary; not independently reviewed; no priority claimed).

## Statement

1. **Attractor lemma.**
   - *Setting.* Let `H ≤ Homeo(X)`, with `X` Hausdorff, and let `t ∈ H` have a fixed point `p`
     whose basin `B(p) = {x : t^n x -> p}` is open and dense and contains a neighbourhood `U`
     of `p` with `t^n x -> p` for `x ∈ U`.
   - *Fixing p.* Every `g ∈ C_H(t)` fixes `p` if `p` is the only fixed point of `t` whose
     basin is open and dense. In general this holds for a subgroup of `C_H(t)` of index at
     most the number of such points.
   - *Conclusion.* The germ map `Stab_(C_H(t))(p) -> (H)_p` is injective.
2. **Diagonal flows in 2V.**
   - *The flow z.* Let `z ∈ V` be north-south, with fixed points `0^∞` (attracting, germ
     `0w -> 00w`) and `1^∞` (repelling, germ `11w -> 1w`), and `z^n x -> 0^∞` for every
     `x != 1^∞`. An example is `z = [0 -> 00, 10 -> 01, 11 -> 1]`.
   - *Conclusion.* For `p, q != 0`, the centralizer in `2V` of `t = z^p × z^q` is
     `<z × 1, 1 × z> ≅ Z^2`.

## Proof

- **(1) Fixing p.** If `g t = t g`, then `g(p)` is a fixed point of `t` with basin `g(B(p))`,
  which is open and dense. If `p` is the only such point, then `g(p) = p`. Otherwise `C_H(t)`
  permutes the finitely many such points, and the stabilizer of `p` has finite index.
- **(1) Injectivity.**
  - Let `g, g' ∈ C_H(t)` fix `p` and have the same germ there, so `g = g'` on a neighbourhood
    `U'` of `p`.
  - For `x ∈ B(p)`, `t^n x ∈ U'` for large `n`. Then
    `g x = t^(-n) g t^n x = t^(-n) g' t^n x = g' x`.
  - So `g = g'` on the dense set `B(p)`, hence everywhere.
- **(2) The attractor.**
  - The fixed points of `t` are the four corners `{0^∞, 1^∞}^2`. Exactly one corner `c` is
    attracting on the dense open set `Ω = (C_2 ∖ {0^∞,1^∞})^2`: it is `(0^∞ or 1^∞)` in each
    coordinate according to the signs of `p` and `q`.
  - `c` has a neighbourhood that is attracted, since `z^(±1)` contracts a cylinder around its
    attracting point.
  - The other corners have basins inside lines, which are nowhere dense. So (1) applies with
    `p = c`.
- **(2) The germ group at c.**
  - A 2V element fixing `c` is near `c` a product of prefix replacements `u x -> u' x`,
    `v y -> v' y`, with `u, u'` prefixes of `c_1` and `v, v'` prefixes of `c_2`.
  - Because the periods have length 1, its germ is `σ_1^a σ_2^b`, where `σ_i` is the germ of
    the corresponding coordinate flow. Here we use that `z` has unit-shift germs at both of
    its fixed points.
  - So `(2V)_c ≅ Z^2`, and every `g ∈ C_2V(t)` has the same germ as some `(z×1)^a (1×z)^b`.
- **(2) Conclusion.** By injectivity, `g = (z×1)^a (1×z)^b`. Conversely, the coordinate flows
  commute with `t`. ∎

## Consequence for graph manifolds

- **The design that dies.** Take the design in which a JSJ torus is realized by coordinate flows
  of `2V` and the other block's fiber is a diagonal `z^p × z^q`. That fiber commutes with no
  free group. So its block `F_w × Z` cannot be realized, which answers the local question of
  `research/artifacts/gq-bh-bh-free-21-automatic-germ-extensions.md` §7.5 negatively for
  north-south `z`.
- **What survives.** Any realization in `2V`, or in a germ extension of `V`, must give every
  Seifert fiber either no dense-basin attractor, or an attractor whose germ group contains the
  whole block. In a germ extension of `V`, that means a singular point with spiral germ group
  `⊇ F × Z`, as in the fiber-first normal form.

## Lesson for general BH

- **Centralizers are local.** A group element with a global attractor has its whole centralizer
  inside one germ group. In Thompson-like hosts (`V`, `nV`, germ extensions of `V`), germ groups
  are small (`Z^n`) or spiral. So inputs with large centralizers of infinite-order elements need
  hosts whose germ groups contain those centralizers.
- **Seifert blocks are the clearest example.** A subgroup `C × Z` whose central generator has a
  dense-basin attractor needs a host germ group that contains `C × Z`.
- **The design rule.** A universal compiler must put the input's centralizers into its germ
  groups, which again says the germs must come from the input.
