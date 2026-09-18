---
rg: 2
id: robertson-steger-word-products-and-boundary-topology
kind: claim
title: "Robertson–Steger: the finite alphabet, restriction of decorated words, unique factorization (H1) and Corollary 4, finiteness of decorations through the injective map δ, and the boundary as a compact Hausdorff totally disconnected space"
distinct_from:
  robertson-steger-boundary-cylinders-and-pure-infiniteness: that imports the relations (rel1), the formula for φ, Lemmas c1 and c2, main2 and the remark after it, and states Corollary 4 only as existence of the product; this imports the word-level conventions those statements rest on (finite alphabet, the restriction convention for decorated words, the uniqueness in (H1) and Corollary 4 with its proof formula, injectivity of δ) and the topology of the boundary.
  robertson-steger-a2-boundary-algebras-are-rank-two-ck: that imports the isomorphism φ and the hypotheses (H0)-(H3) as structure theorems; this imports the word conventions and the boundary topology verbatim.
---

**ESTABLISHED (import)** through `robertson-steger-word-products-and-boundary-topology-citation`.

Source: G. Robertson, T. Steger, *Affine buildings, tiling systems and higher rank
Cuntz–Krieger algebras*, J. reine angew. Math. 513 (1999), arXiv:1302.5593, TeX source
`CK1.tex`. The quotes are copied from the source. Only macros are expanded: `\ow`, `\ou`
are `w̄`, `ū`; `\G` is `Γ`; `\cB` is `B`; `\Om` is `Ω`; `\fT`, `\ft`, `\fP`, `\ofW` are
`𝔗`, `𝔱`, `𝔓`, `𝔚̄`; `\s` is `σ`.

## Word conventions (Section 1, verbatim)

1. (line 200) "We fix a finite set `A` (an "alphabet")."
2. (lines 205-213) "`W_{[m,n]} = { w: [m,n] → A ; M_j(w(l+e_j),w(l)) = 1 whenever
   l, l+e_j ∈ [m,n] }`. Put `W_m = W_{[0,m]}` if `m ≥ 0`. Say that an element `w ∈ W_m`
   has *shape* `m`, and write `σ(w) = m`. [...] Define the initial and final maps
   `o: W_m → A` and `t: W_m → A` by `o(w) = w(0)` and `t(w) = w(m)`."
3. (lines 214-221) "Fix a nonempty finite or countable set `D` (whose elements are
   "decorations"), and a map `δ: D → A`. Let `W̄_m = { (d,w) ∈ D × W_m ; o(w) = δ(d) }`,
   the set of "decorated words" of shape `m`, and identify `D` with `W̄_0` via the map
   `d ↦ (d,δ(d))`. [...] Define `o: W̄_m → D` and `t: W̄_m → A` by `o(d,w) = d` and
   `t(d,w) = t(w)`."
4. (lines 225-232) "Given `j ≤ k ≤ l ≤ m` and a function `w: [j,m] → A`, define
   `w|_{[k,l]} ∈ W_{l-k}` by `w|_{[k,l]} = w'` where `w'(i) = w(i+k)` for
   `0 ≤ i ≤ l-k`. If `w̄ = (d,w) ∈ W̄_m`, define `w̄|_{[k,l]} = w|_{[k,l]} ∈ W_{l-k}` if
   `k ≠ 0`, and `w̄|_{[0,l]} = (d, w|_{[0,l]}) ∈ W̄_l`."
5. (lines 244-247) "(H1) Let `u ∈ W_m` and `v ∈ W_n`. If `t(u) = o(v)` then there exists
   a unique `w ∈ W_{m+n}` such that `w|_{[0,m]} = u` and `w|_{[m,m+n]} = v`." (Definition
   `word-prod`: "In the situation of (H1) we write `w = uv` and say that the product `uv`
   exists.")
6. (lines 461-471) "Corollary 4. If `ū = (d,u) ∈ W̄_m` and `v ∈ W_n` with `t(ū) = o(v)`,
   then there exists a unique `w̄ ∈ W̄_{m+n}` such that `w̄|_{[0,m]} = ū` and
   `w̄|_{[m,m+n]} = v`. In these circumstances we write `w̄ = ūv`, and say that the product
   `ūv` exists. *Proof.* This is immediate, with `ūv = (d,uv)`."

## Boundary data (Section 7, verbatim)

7. (line 1527) "Let `B` be a locally finite thick affine building of type `Ã_2`."
8. (lines 1541-1545) "The boundary `Ω` is a totally disconnected compact Hausdorff space
   with a base for the topology given by sets of the form
   `Ω(v) = { ω ∈ Ω : [O,ω) contains v }` where `v` is a vertex of `B` [CMS, Section 2]."
9. (lines 1546-1547) "Let `Γ` be a group of type rotating automorphisms of `B` that acts
   freely on the vertex set with finitely many orbits."
10. (lines 1597-1599) "Let `𝔗` denote the set of type rotating isometries `i: 𝔱 → B`, and
    let `A = Γ\𝔗`. We will use the set `A` as an alphabet to define an algebra `𝒜`."
11. (lines 1749-1754) "Let `𝔚̄_m` denote the set of type rotating isometries
    `p: 𝔭_m → B` such that `p(0,0) = O` and let `𝔚̄ = ⋃_m 𝔚̄_m`. Let `D` denote the set of
    type-rotating isometries `d: 𝔱 → B` such that `d(0,0) = O`. Let `δ: D → A` be given
    by `δ(d) = Γd`. The map `δ` is injective since `Γ` acts freely on the vertices of `B`."

## Consequences read off (no new mathematics)

- `D` is finite: `δ` is injective into the finite alphabet `A` (items 1, 10, 11).
- For each `m`, `W̄_m ⊆ D × A^{[0,m]}` is finite. Hence `W̄ = ⋃_m W̄_m` is countable.
- Corollary 4 with its proof formula: for `ū = (d,u)` the product is `ūv = (d,uv)`, where
  `uv` is the undecorated (H1) product.

**Verification level.** All items were read in the TeX source (the line numbers above).
The proof of Corollary 4 is quoted in full. Items 8-11 are the standing setting of the
section in which φ and Theorem main2 are proved.
