---
rg: 2
id: kazhdan-orbit-bound-in-amenable-by-free-groups-proof
kind: route
title: "Følner slabs in the amenable factor and a tree centroid in the free factor give a small-boundary half-set, which Kazhdan expansion forbids at large size"
target: kazhdan-orbit-bound-in-amenable-by-free-groups
requires: []
---

Notation as in the target. For `B ⊂ Z` put
`∂B = #{(z, s) ∈ B × S : sz ∉ B}`. Since `S = S^{-1}`, the map `(z, s) ↦ (sz, s^{-1})` is a
bijection between the pairs leaving `B` and the pairs leaving `Z \ B`, so
`∂B = ∂(Z \ B)`. The same map shows: the number of `(z, s)` with `z ∈ B` and `sz ∈ D` is at
most `|S| · |D|`, for any `D ⊂ Z`.

## Step 0. A symmetric generating Kazhdan pair

Let `(Q, ε)` be a Kazhdan pair with `Q` finite, and `H = ⟨Q⟩`. In the quasi-regular
representation on `ℓ²(K/H)` the unit vector `δ_H` is `Q`-fixed, so there is a nonzero
invariant vector. It is constant on the single orbit `K/H` and square summable, so `K/H`
is finite. Let `T` be a finite set of coset representatives and
`S = Q ∪ Q^{-1} ∪ T ∪ T^{-1}`. Then `S` is finite, symmetric and generates `K`, and
`(S, ε)` is a Kazhdan pair because the defining condition only weakens when the set grows.

## Step 1. Expansion of finite transitive sets

Let `Z` be a finite transitive `K`-set and `ℓ²_0(Z)` the functions with sum zero. It is
`K`-invariant, and an invariant vector in it is constant (one orbit) with sum zero, so
zero. Let `∅ ≠ B ⊂ Z` with `|B| ≤ |Z|/2` and `f = 1_B − (|B|/|Z|)·1 ∈ ℓ²_0(Z)`. Then
`||f||² = |B|(1 − |B|/|Z|) ≥ |B|/2`. The Kazhdan pair gives `s ∈ S` with
`||s·f − f||² ≥ ε²||f||²`, and `s·f − f = 1_{sB} − 1_B`, whose squared norm is
`|sB Δ B| = 2|sB \ B|`. As `|sB \ B| = #{z ∈ B : sz ∉ B}` (both equal `|B| − |B ∩ sB|`,
using `|sB| = |B|`),

```text
∂B ≥ ε² |B| / 4        whenever ∅ ≠ B ⊂ Z, |B| ≤ |Z|/2.                   (1)
```

## Step 2. A Følner slab of small boundary

Write `ι(z) = (α(z), τ(z)) ∈ A × F_d`. For each `(z, s)` there is `(a, t) ∈ E` with
`α(sz) = a α(z)` and `τ(sz) = t τ(z)`.

Put `δ = ε²/(128|S|)` and fix an `(E_A, δ)`-Følner set `F`. For `q ∈ A` let
`B_q = {z : α(z) ∈ Fq}`.

- *Mass.* For each `z`, `#{q : α(z) ∈ Fq} = #{q : α(z) q^{-1} ∈ F} = |F|`. So
  `Σ_q |B_q| = |Z| · |F|`, a finite sum with only finitely many nonzero terms.
- *Boundary.* For a pair `(z, s)` with `α(sz) = a α(z)`, the pair leaves `B_q` iff
  `w = α(z) q^{-1}` satisfies `w ∈ F` and `aw ∉ F`. As `q` runs over `A`, `w` runs over `A`
  bijectively, so the number of such `q` is `|F \ a^{-1}F| = |aF \ F| ≤ |aF Δ F| ≤ δ|F|`.
  So `Σ_q ∂B_q ≤ |Z| · |S| · δ|F| = δ|S| · Σ_q |B_q|`.

Since `Z ≠ ∅`, some `B_q` is nonempty, and `∂B_q = 0` when `B_q = ∅`. If every nonempty
`B_q` had `∂B_q > δ|S| |B_q|`, summing would contradict the last inequality. Fix `q` with

```text
B_q ≠ ∅,     ∂B_q ≤ δ|S| · |B_q| = (ε²/128) · |B_q|.                        (2)
```

**Case 1: `|B_q| ≤ |Z|/2`.** Then (1) and (2) give `ε²/4 ≤ ε²/128`, which is false.

**Case 2: `|B_q| > |Z|/2`.** Put `A_0 = B_q`. Then `|A_0| > |Z|/2` and, by (2),
`∂A_0 ≤ (ε²/128)|Z|`. The rest of the proof handles this case.

## Step 3. A tree centroid inside the slab

Let `𝒯` be the left Cayley graph of `F_d` for a free basis: vertices `F_d`, edges
`w ~ xw` for basis letters `x`. It is the image of the right Cayley graph under
`w ↦ w^{-1}`, so it is a `2d`-regular tree, and `d_𝒯(w, w') = |w' w^{-1}|`. Hence
`d_𝒯(τ(z), τ(sz)) = |t| ≤ R` for every pair `(z, s)`. (For `d = 0`, `𝒯` is one vertex.)

*Fibres.* On `A_0`, `α` takes values in `Fq`, and `ι` is injective. So for every vertex
`u`, `#{z ∈ A_0 : τ(z) = u} ≤ |F|`, and for every ball,
`#{z ∈ A_0 : τ(z) ∈ B_𝒯(u, R)} ≤ |F| · |B_𝒯(R)| = C`.

*Centroid.* Give each vertex `u` the weight `m(u) = #{z ∈ A_0 : τ(z) = u}`, of total
`W = |A_0|`. There is a vertex `v` such that every component of `𝒯 \ {v}` has weight
`≤ W/2`. Proof: at most one side of each edge has weight `> W/2`. If some edge `{u, u'}`
has neither side `> W/2`, take `v = u`: the component of `𝒯 \ {u}` through `u'` is the
`u'`-side, and the other components lie in the `u`-side. Otherwise orient every edge
toward its heavy side and walk along orientations from a vertex of the support of `m`.
The walk never reverses an edge, since an edge cannot point both ways. It never leaves
the finite subtree spanned by the support of `m`, because an edge leaving that subtree
has weight `0` on its far side, so it points back in. A non-backtracking walk in a finite
tree stops, at a vertex `v` all of whose edges point in. So every component of
`𝒯 \ {v}` has weight `≤ W/2`.

*Core and branches.* Let `C_0 = {z ∈ A_0 : d_𝒯(τ(z), v) ≤ R}`, so `|C_0| ≤ C`. Every
`z ∈ A_0 \ C_0` has `τ(z)` in one component (*branch*) of `𝒯 \ {v}`. If `z`, `sz` both lie
in `A_0 \ C_0` in different branches, the geodesic from `τ(z)` to `τ(sz)` passes through
`v`, so its length is `> 2R ≥ R`. That contradicts `d_𝒯(τ(z), τ(sz)) ≤ R`. So:

```text
no pair (z, s) joins two different branches of A_0 \ C_0.                    (3)
```

*Grouping.* Let `W_out = |A_0 \ C_0| ≥ |A_0| − C`. If `W_out = 0`, then
`|Z| < 2|A_0| ≤ 2C ≤ M`, and we are done. Otherwise, each branch part of `A_0 \ C_0` has at
most `W/2 = |A_0|/2` points. If some branch part has at least `W_out/4` points, let `B` be
that part. If not, add branch parts one at a time until the total first reaches
`W_out/4`, and let `B` be their union. It then has fewer than `W_out/4 + W_out/4` points.
In both cases `B` is a nonempty union of whole branch parts, and

```text
W_out/4 ≤ |B| ≤ |A_0|/2 ≤ |Z|/2.                                            (4)
```

## Step 4. The bound

Count the pairs `(z, s)` with `z ∈ B` and `sz ∉ B`.

- `sz ∉ A_0`: at most `∂A_0 ≤ (ε²/128)|Z|` pairs.
- `sz ∈ C_0`: at most `|S| · |C_0| ≤ |S| C` pairs.
- `sz ∈ A_0 \ C_0`: then `sz` is in a different branch from `z`, since `B` contains
  whole branch parts. This is impossible by (3).

So `∂B ≤ |S| C + (ε²/128)|Z|`. By (4), `B` satisfies the hypotheses of (1). Also
`|B| ≥ W_out/4 ≥ (|A_0| − C)/4 ≥ (|Z|/2 − C)/4`. Hence

```text
(ε²/16) · (|Z|/2 − C)  ≤  (ε²/4)|B|  ≤  ∂B  ≤  |S| C + (ε²/128)|Z|.
```

Rearranging, `(ε²/32 − ε²/128)|Z| = (3ε²/128)|Z| ≤ C(|S| + ε²/16)`, that is,

```text
|Z| ≤ C · (128|S|/(3ε²) + 8/3) = M.
```

`M` depends only on `|S|`, `ε`, the Følner set `F` (chosen in `A` from `E_A`, `|S|` and
`ε`), `d` and `R`. It does not depend on `Z` or `ι`. ∎
