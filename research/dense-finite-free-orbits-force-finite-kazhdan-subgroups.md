---
rg: 2
id: dense-finite-free-orbits-force-finite-kazhdan-subgroups
kind: claim
title: "For a continuous action of A × F_d (A amenable) on a compact space, a Kazhdan subgroup of the topological full group is finite as soon as its finite orbits through free points are dense; on Ω × ∂F_d it is finite iff it has no infinite orbit through a free point"
distinct_from:
  kazhdan-subgroups-of-brin-thompson-groups-are-finite: that asks for finiteness in nV, reduced to orbit finiteness by a route through germ characters and bounded offsets on C^n; this is a reduction for transformation-groupoid full groups of A × F_d through a uniform orbit bound and closedness, and applies to the boundary-product host, which is not an nV.
  kazhdan-subgroups-of-nv-act-with-finite-orbits: that is the open orbit-finiteness problem for nV; this settles the analogous reduction step for (Z^2 × F_d) ⋉ (Ω × ∂F_d) and leaves an orbit-finiteness problem of the same shape there.
  af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan: that exhibits an infinite Kazhdan group in the full group of a lattice boundary action, where the acting group is itself Kazhdan; this shows that for acting groups A × F_d with A amenable an infinite Kazhdan subgroup needs infinite orbits through free points.
---

**ESTABLISHED** by `dense-finite-free-orbits-force-finite-kazhdan-subgroups-proof`.

## Setting

- `P = A × F_d`, with `A` countable amenable and `d ≥ 0`, acts continuously on a compact
  Hausdorff space `X`.
- `[[P ⋉ X]]` is the group of homeomorphisms `g` of `X` for which there is a continuous
  `c_g : X → P` (so of finite range) with `g(x) = c_g(x) · x`.
- `X_free = {x : Stab_P(x) = 1}`.

## Theorem

Let `K ≤ [[P ⋉ X]]` have property (T). Suppose the set
`{x ∈ X_free : Kx is finite}` is dense in `X`. Then there is `M` with `|Kx| ≤ M` for
every `x ∈ X`, and `K` is finite.

## Corollary (the boundary-product host)

Suppose `X_free` is dense, for instance
`X = Ω × ∂F_d` with `P = Z^2 × F_d` acting diagonally, `Ω` a free `Z^2`-subshift and
`d ≥ 2`. Then for a Kazhdan `K ≤ [[P ⋉ X]]` the following are equivalent:

1. `K` is finite;
2. every `K`-orbit through a point of `X_free` is finite;
3. the `K`-orbits through points of `X_free` have bounded size.

For `Ω × ∂F_d`: `(a, w)` fixes `(ω, ξ)` iff `a·ω = ω` and `w·ξ = ξ`. Freeness of `Ω` forces
`a = 0`. A nontrivial `w` fixes exactly the two endpoints of its axis. So `X_free` is `Ω`
times the complement of a countable set in `∂F_d`, which has no isolated points. Hence
`X_free` is dense.

So an infinite Kazhdan subgroup of the monomial unit group `[[·]]` of the target host
`B_Ω ⊗ L_∂` of `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` must have
an infinite orbit `Z = Kx` through a free point. The map `kx ↦ (the unique p ∈ P with
kx = px)` then injects `Z` into `Z^2 × F_d` with bounded left displacement.

- The Schreier graph of `Z` is non-amenable: `ℓ²(Z)` has no invariant vector, and the
  Kazhdan pair gives `∂B ≥ ε²|B|/2` for every finite `B ⊂ Z`.
- The `F_d`-coordinate spreads exponentially. Take vertex boundaries: a set `B` with
  edge boundary `≥ c|B|` has at least `c|B|/|S|` outside neighbours. So balls of the
  Schreier graph satisfy `|B_Z(z, n)| ≥ (1 + c/|S|)^n`, with `c = ε²/2`. The `Z^2`-coordinate
  of `ι(B_Z(z, n))` lies in a Euclidean ball of radius `O(n)`, which has `O(n²)` points.
  Since `ι` is injective, the `F_d`-coordinate takes at least
  `(1 + c/|S|)^n / O(n²)` values on `B_Z(z, n)`. In particular it is unbounded. The
  orbit must travel in the tree direction, which is exactly where `∂F_d` carries no
  invariant measure (see Attempts on the target).

**Residual question (OPEN, not a node).** Does some infinite Kazhdan group act
transitively on an infinite set `Z` admitting an injective map to `Z^2 × F_d` with bounded
left displacement? Graph-level properties do not decide it: `Cay(F_d × Z^2)` is
non-amenable, one-ended, and injects. A negative answer, together with this Corollary,
makes all Kazhdan subgroups of `[[(Z^2 × F_d) ⋉ (Ω × ∂F_d)]]` finite.

DERIVATION
dense-finite-free-orbits-force-finite-kazhdan-subgroups-proof
