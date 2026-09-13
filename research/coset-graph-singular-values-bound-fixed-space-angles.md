---
rg: 2
id: coset-graph-singular-values-bound-fixed-space-angles
kind: claim
title: The second singular value of a finite coset graph bounds the fixed-space angle cosine in every unitary representation
---

**Setting.** `A` is a finite group and `H, K <= A` are subgroups with `<H, K> = A`. The coset graph
`Γ_A(H, K)` is bipartite, with vertex set `A/H ⊔ A/K` and one edge `gH — gK` for each `g ∈ A`. Let `M` be
its biadjacency matrix, `M_{aH, bK} = |aH ∩ bK|`, and let `σ_2` be the square root of the second largest
eigenvalue, counted with multiplicity, of `T = MM^T / (|H||K|)` on `ℓ^2(A/H)`. The largest eigenvalue
is `1`, on the constants.

**ESTABLISHED.**
1. `σ_2 = max_{π ∈ Irr(A), π ≠ 1} ‖P_{π^H} P_{π^K}‖`. This is the representation angle `ε_A(H, K)` of
   Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, §2.1.
2. Let `Λ` be any group with a homomorphism `A -> Λ`, and let `V` be a unitary representation of `Λ`.
   Then `V^H ∩ V^K = V^A`, and the Friedrichs cosine satisfies `cos ∢(V^H, V^K) <= σ_2`.

So the pairwise hypotheses of `kassabov-subspace-angle-criterion`, for subgroups that pairwise generate
finite groups, can be checked on finite coset graphs.

Proof: `coset-graph-singular-values-bound-fixed-space-angles-proof`. The statement is standard: CCKW
§2.3 relate the representation angle to the spectral gap of the coset graph, following
Dymara–Januszkiewicz and Oppenheim. No novelty is claimed.
