---
rg: 2
id: thompson-f-f-times-z-f-times-f-are-mutual-subgroups-proof
kind: route
title: "Dyadic subintervals give copies of F, disjoint supports give products, and subgroup inclusions are coarse embeddings"
target: thompson-f-f-times-z-f-times-f-are-mutual-subgroups
requires: []
---

F is the group of orientation-preserving piecewise-linear homeomorphisms of
`[0,1]` with finitely many breakpoints, all at dyadic rationals, and slopes powers
of 2 (Cannon–Floyd–Parry). Such maps send dyadic rationals to dyadic rationals.

**Item 1.** Let `a = p/2^n < b = q/2^n`. Then `[a,b]` is the union of the `q - p`
standard dyadic intervals `[i/2^n, (i+1)/2^n]`. Repeatedly bisecting standard
dyadic intervals partitions `[0,1]` into any prescribed number `m ≥ 1` of standard
dyadic intervals; take `m = q - p`. The map `h: [0,1] -> [a,b]` sending the `j`-th
piece of `[0,1]` affinely and increasingly onto the `j`-th piece of `[a,b]` is a
homeomorphism with dyadic breakpoints and slopes powers of 2, sending dyadic
rationals to dyadic rationals. For `φ ∈ F`, the map equal to `h φ h^{-1}` on
`[a,b]` and to the identity elsewhere has finitely many dyadic breakpoints and slopes
powers of 2, so it lies in `F_[a,b]`. The inverse assignment `ψ ↦ h^{-1} ψ|_[a,b] h`
maps `F_[a,b]` into F. Both assignments are homomorphisms and inverse to each
other, so `F_[a,b] ≅ F`.

**Item 2.** Elements with disjoint supports commute, and `F_[0,1/2] ∩ F_[1/2,1]` is
trivial, so the product `F_[0,1/2] · F_[1/2,1]` is an internal direct product,
isomorphic to `F × F` by Item 1. It is exactly the stabilizer of `1/2`: an element
fixing `1/2` restricts to elements of `F_[0,1/2]` and `F_[1/2,1]`. F is torsion-free,
since an orientation-preserving homeomorphism of an interval of finite order is the
identity. So for any nontrivial `z ∈ F_[1/2,1]`, the subgroup `F_[0,1/2] · <z>` is
isomorphic to `F × Z`.

**Item 3.** F is isomorphic to `F × {1} ≤ F × Z`, and `F × Z` is isomorphic to a
subgroup of `F × F` (using `Z ≅ <z> ≤ F`). By Item 2 both products embed in F. So
each of the three groups embeds in each of the others. If `K ≤ G` are finitely
generated with word metrics `d_K`, `d_G`, the inclusion is Lipschitz, and
`d_G(k,k') <= R` forces `k^{-1}k'` into the finite set `B_G(R) ∩ K`, whose `d_K`-lengths
are bounded by some `ρ(R)`. So the inclusion is a coarse embedding with uniformly
bounded fibres.

**Item 4.** Choose disjoint dyadic intervals `I_1, …, I_n` and nontrivial
`z_i ∈ F_{I_i}`. The `z_i` commute and generate a copy of `Z^n`. Asymptotic dimension
is monotone under coarse embeddings, and `asdim Z^n = n`, so `asdim F >= n` for every
`n`. ∎
