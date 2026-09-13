---
rg: 2
id: cocompact-building-lattices-have-dense-strongly-regular-poles
kind: claim
title: Uniform lattices on locally finite thick Euclidean buildings have strongly regular elements with poles dense in the opposite pairs of chambers
distinct_from:
  strongly-regular-building-elements-are-opposition-proximal: that is about the dynamics of one strongly regular element; this asks that the pole pairs of the strongly regular elements of a uniform lattice be dense.
---

**OPEN.** Let `Γ` act properly and cocompactly by type-preserving automorphisms
on a locally finite thick Euclidean building `X`. The claim is that the pairs
`(c₊(a), c₋(a))`, where `a` runs over the strongly regular hyperbolic elements
of `Γ`, are dense in the set of pairs of opposite chambers of `∂X`, with the
cone topology.

## Attempts

1. **Existence (literature).** Caprace--Ciobotaru, arXiv:1304.6210v2, Theorem
   1.2: a group acting cocompactly on a locally finite Euclidean building
   contains a strongly regular hyperbolic element. They note the discrete case
   also follows from Ballmann--Brin.
2. **Closing along one side (literature).** Their Proposition 2.9 applies to a
   strongly regular line `ρ` whose special vertices at regular spacing fall into
   finitely many `Γ`-orbits, which cocompactness gives. It yields strongly
   regular `h_{m,n} ∈ Γ` whose axes contain `[ρ(t_{f(m)}), ρ(t_{f(n)})]`.
   - **What it controls.** The axes share long forward segments of `ρ`, so it
     controls the attracting endpoint.
   - **Why the repelling side is out of reach.** The subsequence `f` comes from
     a compactness argument, so `t_{f(1)}` isn't bounded. The source gives no
     axis containing `[ρ(−T), ρ(T)]` for large `T`, which is what
     simultaneous control of both poles needs.
