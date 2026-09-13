---
rg: 2
id: non-vtf-hyperbolic-counterexample-may-be-one-ended-proof
kind: route
title: Pass to vertex quotients by torsion-free normal subgroups and use virtual freeness of graphs of finite groups
target: non-vtf-hyperbolic-counterexample-may-be-one-ended
requires: []
---

**Theorem.** Let `G = π_1(𝒢)`, where `𝒢` is a finite graph of groups with finite edge
groups `G_e` and virtually torsion-free vertex groups `G_v`.

1. Let `N_v` be the normal core in `G_v` of a torsion-free finite-index subgroup. It is
   torsion-free, normal and of finite index. Since `G_e` is finite, `G_e ∩ N_v = 1`, so
   each edge monomorphism `G_e -> G_v` descends to a monomorphism into `G_v/N_v`.
2. This gives a finite graph of finite groups `𝒢'` with vertex groups `G_v/N_v` and the
   same edge groups, and a surjection `π: G -> π_1(𝒢')` restricting to the quotient
   maps on the vertex groups.
3. `π_1(𝒢')` is virtually free, being the fundamental group of a finite graph of
   finite groups (Serre, *Trees*, II.2.6), hence virtually torsion-free. Let
   `ψ: π_1(𝒢') -> F` be a homomorphism to a finite group with torsion-free kernel. It
   is injective on every finite vertex group `G_v/N_v`.
4. Put `φ = ψ ∘ π`. Then `ker(φ) ∩ G_v = N_v` is torsion-free.
5. A finite subgroup `K <= G` fixes a vertex of the Bass–Serre tree, so
   `K <= g G_v g^-1` for some `v` and `g`, and `K ∩ ker(φ) <= g N_v g^-1 ∩ K = 1`. So
   `ker(φ)` is a torsion-free subgroup of finite index.

**Corollary.** A word-hyperbolic group is finitely presented, so by Dunwoody's
accessibility theorem it is the fundamental group of a finite graph of groups with
finite edge groups and vertex groups with at most one end. Vertex groups of a
splitting over finite subgroups of a hyperbolic group are quasiconvex, hence
hyperbolic. Finite vertex groups are virtually torsion-free. By the Theorem, if `G` is
not virtually torsion-free, some one-ended vertex group is not. The converse
direction of the "iff" is trivial.
