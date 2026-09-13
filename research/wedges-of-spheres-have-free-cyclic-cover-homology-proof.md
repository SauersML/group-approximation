---
rg: 2
id: wedges-of-spheres-have-free-cyclic-cover-homology-proof
kind: route
title: "Proof: infinite cyclic covers of wedges of spheres have free homology over k[t^{±1}]"
target: wedges-of-spheres-have-free-cyclic-cover-homology
requires: []
---

**Part 1.** Let `f: T → W` be a homotopy equivalence with
`W = ∨_{i∈I} S^{n_i}`. A connected infinite cyclic covering of `T` corresponds
to a surjection `φ: π_1(T) → Z`. Transport it along `f_*` to a surjection
`π_1(W) → Z`, and let `W̃ → W` be the associated covering. Lifting `f` and a
homotopy inverse, together with the homotopies between the composites and the
identities (covering homotopy property), gives a `t`-equivariant homotopy
equivalence `T̃ ≃ W̃`. So it suffices to treat `W`.

Write `W = Γ ∨ W'`, where `Γ` is the wedge of the circles (`n_i = 1`) and `W'`
the wedge of the spheres of dimension `≥ 2`, glued at the base point `*`.
`π_1(W) = π_1(Γ)` is free, and `W'` is simply connected. The preimage of `W'`
in `W̃` is therefore a disjoint union of copies `t^j W'`, `j ∈ Z`, each
attached to the connected covering graph `Γ̃` at one lift `t^j *` of the base
point. (`Γ̃` is connected because `φ` is onto.) Attaching spaces along single
points adds their reduced homology, so for `q ≥ 2`

  `H_q(W̃; k) = ⊕_{j∈Z} H_q(t^j W'; k) ≅ k[t^{±1}] ⊗_k H_q(W'; k)`,

which is free. For `q = 1`, `H_1(W̃; k) = H_1(Γ̃; k)` is the kernel of the
boundary map `C_1(Γ̃; k) → C_0(Γ̃; k)`. It is a submodule of the free
`k[t^{±1}]`-module `C_1(Γ̃; k)`, and submodules of free modules over the
principal ideal domain `k[t^{±1}]` are free (for arbitrary rank). Finally
`H_0(W̃; k) = k`, on which `t` acts trivially, which is `k[t^{±1}]/(t − 1)`.

**Part 2.** `C = C_*(T̃; k)` is a complex of free `k[t^{±1}]`-modules. For the
module `k_λ = k[t^{±1}]/(t − λ)`, the universal coefficient theorem over a
principal ideal domain gives

  `H_q(C ⊗ k_λ) ≅ (H_q(C) ⊗ k_λ) ⊕ Tor(H_{q−1}(C), k_λ)`.

By Part 1, a wedge has `H_q(C) ≅ k[t^{±1}]^{m_q}` for `q ≥ 1` (with `m_q`
finite when `T` is finite, since `H_q(C) ⊗ k_1` is then finite-dimensional),
and `H_0(C) = k[t^{±1}]/(t − 1)`. Then `H_q(C) ⊗ k_λ = k^{m_q}` for every `λ`.
The Tor term vanishes when `H_{q−1}(C)` is free, i.e. for `q ≥ 2`. For
`q = 1`, `Tor(k[t^{±1}]/(t − 1), k_λ)` is `k` if `λ = 1` and `0` otherwise.
Hence `b_q(λ) = m_q` for `q ≥ 2` and every `λ`, while `b_1(λ) = m_1 + [λ = 1]`.
Also `C ⊗ k_1 = C_*(T; k)`, which gives `b_q(1) = dim H_q(T; k)`.

**The planar covering.** If `p ∉ S(X; r)`, the angle map is continuous on
`|T|`, since every simplex projects to a convex set avoiding `p`. For each
vertex `v` take the angle `θ(v) ∈ [0, 2π)`. For an edge `uv` let
`c(u, v) = (θ(u) + δ − θ(v))/2π ∈ {−1, 0, 1}`, where `δ ∈ (−π, π)` is the
signed angle subtended by the segment `uv` at `p`. On each triangle the
integers `c` form a cocycle, because the triangle avoids `p`. Lift the simplex
`[v_0, …, v_q]` so that `v_0` lies on sheet `0`. Then the face opening at
`v_1` carries the coefficient `t^{c(v_0, v_1)}` and all other faces carry
coefficient `1`, with the usual signs. This is the cellular chain complex of
the pulled-back covering.
