---
rg: 2
id: nonamenable-edges-break-division-ring-compatibility
kind: claim
title: Amenability of edge groups is sharp for arbitrary vertex division rings, since k[F2 x Z] embeds epically in the Heisenberg Ore field with the Z-transversal of F2 dependent over the closure of F2
distinct_from:
  amenable-edge-graphs-of-groups-preserve-division-ring-embeddings: that proves the positive theorem for amenable edges, where the edge closure is an Ore localisation and transversals are automatically independent; this shows that for the non-amenable edge F2 the independence step can fail for a legitimate epic vertex embedding, so the arbitrary-vertex-ring hypothesis cannot be kept once edges are non-amenable.
  compatible-graphs-of-groups-with-loops-embed-in-division-rings: that proves embedding from D-compatibility (transversal independence); this builds an explicit vertex embedding violating it, and a two-vertex graph where the Cohn-coproduct construction is not injective.
  vertex-division-closure-escapes-edge-coset-span: that says the vertex closure is not in the edge-coset span; this says the edge closure can already swallow the whole vertex closure.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this kills the arbitrary-vertex-ring coproduct construction over non-amenable edges.
---

**ESTABLISHED** by [[nonamenable-edge-compatibility-counterexample-proof]]. It rests on Bell--Rogalski's criterion and Lichtman's
valuation corollary as quoted and applied by Sanchez (arXiv:1206.7013); Lichtman's paper itself was not re-read.
Not yet independently re-derived.

Let `k0` be any field, `lambda` transcendental over `k0`, `l = k0(lambda)`, `K = l(t)`, `sigma` the
`l`-automorphism of `K` with `t -> lambda t`, and `Q` the Ore field of `K[X; sigma]` (relation `aX = X a^sigma`).
Then `Q` is the Ore field of `k0[H3]`, for `H3` the Heisenberg group. Let `alpha = (1-X)^-1`, `g = (1-t)^-1`, and
`u = alpha`, `v = 1 + (alpha - 1) g alpha (alpha - 1)`.

**Theorem.** Put `V = F2 x Z = <a, b> x <w>` and `C = <a, b> = F2`. The assignment `a -> u`, `b -> v`, `w -> lambda`
extends to an injective ring homomorphism `k0[V] -> Q` with these properties:
1. **It is epic.** Already `Div(k0[C]) = Q`.
2. **Transversals are dependent.** The right transversal `{w^n}` of `C` in `V` is left-dependent over
   `Div(k0[C]) = Q`, via `1*w - lambda*1 = 0`.

So the embedding is not Linnell. Since `V` is locally indicable, Linnell is equivalent to Hughes-free (Grater, Cor.
8.3), so the embedding is not Hughes-free either.

**Corollary (sharpness of the amenable-edge hypothesis).** Let `G = V *_C V' = F2 x (Z * Z)`, with the embedding
above on both vertices. The edge closure in each vertex is `D_C = Q = D_V`, so the Cohn coproduct
`D_V *_(D_C) D_V'` is `Q`. The map `k0[G] -> Q` sends `w - w'` to `lambda - lambda = 0`, so it is not injective.

The positive theorem `amenable-edge-graphs-of-groups-preserve-division-ring-embeddings` takes arbitrary vertex
division rings. Its compatibility step (edge closure is a localisation, so transversals are independent) holds for
every amenable edge. By Bartholdi (`k[C]` Ore implies `C` amenable) it can only be a localisation argument for
amenable edges, and this example shows it genuinely fails for the first non-amenable edge `F2`. Any iteration over
non-amenable edges must therefore restrict the vertex embeddings, for example to Hughes-free or universal ones.

**What it does not kill.** `k0[F2 x F2]` does embed in a division ring (Hughes-free). The obstruction is to the
construction with arbitrary vertex rings, not to the permanence statement for non-amenable edges, which stays open.
