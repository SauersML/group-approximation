---
rg: 2
id: cat0-cube-complexes-have-the-jensen-helly-property
kind: claim
title: Every median graph of finite cube dimension k ≥ 1 (the 1-skeleton of a k-dimensional CAT(0) cube complex) has the Jensen–Helly property of dimension k
distinct_from:
  raag-salvetti-covers-have-the-jensen-helly-property: that is the special case of RAAG Salvetti covers, with k the clique number; this claims the property for every median graph of finite cube dimension, with no group in sight
  cograph-salvetti-covers-have-the-jensen-helly-property: that covers only Salvetti covers of P4-free graphs, through products and one-vertex wedges; this covers every finite-dimensional CAT(0) cube complex at once
---

Let `G` be a connected median graph with vertex set `V`, path metric `d` and
hyperplanes `H`. By Chepoi and Roller, these are exactly the 1-skeleta of
CAT(0) cube complexes (standard). Fix a base vertex `o` and give each vertex
`v` the coordinates `c_v(h) = [h separates o and v] ∈ {0,1}^H`. A
**coordinate cube** `(v,F)` is a vertex `v` and a finite set `F ⊆ H` such that
all `2^{|F|}` patterns on `F`, with `c_v` off `F`, are vertex vectors. Put:

- `k` = the largest `|F|`, called the cube dimension. For a CAT(0) cube
  complex this is its dimension (standard, not re-proved here; the claim is
  stated and proved for the cube dimension, and applications such as
  `raag-salvetti-covers-jensen-helly-via-cube-complexes` bound the cube
  dimension directly).
- `|X|` = the union of the faces `{p : p = c_v off F, p ∈ [0,1]^F}` of the box
  `[0,1]^H`.
- `d_1(p,p') = Σ_h |p_h − p'_h|`.

**Claim.** If `1 ≤ k < ∞`, then `(|X|, d_1)` contains `(V,d)` isometrically
and satisfies, in the sense of
`jensen-helly-graphs-have-contractible-rips-complexes`:
- **(J) Jensen barycentres.** Every finitely supported probability measure
  `μ` on `V` has a point `b ∈ |X|` with `d_1(x,b) ≤ ∫ d(x,y) dμ(y)` for all
  `x ∈ V`.
- **(H) Helly number `k+1`** for balls centred at vertices.
- **(R) Rounding.** Every point is within `k/2` of a vertex.

So `G` has the Jensen–Helly property of dimension `k`. Bounded degree is not
assumed.

Sharpness of the Helly number: in `R^3 = |X|` for `Z^3`, there are four l^1-balls
any three of which meet while all four do not (the example is in the artifact).

UNREVIEWED (one swarm referee pass, 2026-09-16, found no error). Proof: route
`cat0-cube-complexes-have-the-jensen-helly-property-proof`.
