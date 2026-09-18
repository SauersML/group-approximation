---
rg: 2
id: robertson-steger-boundary-cylinders-and-pure-infiniteness
kind: claim
title: "Robertson–Steger: the boundary cylinders Ω(p) partition Ω and form a basis, φ(s_{w̄2,w̄1}) = γ1_{Ω(p1)}, C(Ω)⋊Γ is simple, purely infinite and equal to the reduced crossed product, and concrete PGL_3 lattice examples exist"
distinct_from:
  robertson-steger-a2-boundary-algebras-are-rank-two-ck: that imports the isomorphism φ, the hypotheses (H0)–(H3) and the irreducibility theorems; this imports the further statements used to read the isomorphism as a piecewise prefix replacement. These are the defining relations (rel1), the formula for φ on generators, Lemmas c1 and c2, the claim inside the proof of main2, the remark after main2 (simple, purely infinite, full = reduced) and the existence of examples.
---

**ESTABLISHED (import)** through `robertson-steger-boundary-cylinders-citation`.

## Setting

- `B` is an affine building of type Ã₂ with boundary `Ω`, and `O` is a fixed vertex.
- `Γ` acts on `B` by type rotating automorphisms, freely on the vertex set, with
  finitely many orbits.
- `A`, `M_1`, `M_2`, `W`, `W̄`, `D` are the Robertson–Steger data of §7:
  - `W̄_m` is the set of decorated words of shape `m ∈ Z²_+`;
  - for `ū ∈ W̄` and `w ∈ W` with `o(w) = t(ū)`, the concatenation `ūw ∈ W̄`
    has shape `σ(ū) + σ(w)`.
- `𝔚̄_m` is the set of type rotating isometries `p: 𝔭_m -> B` with `p(0,0) = O`.
- `ᾱ: 𝔚̄_m -> W̄_m` is a bijection (Lemma `oalpha`).
- `Ω(p) = {ω ∈ Ω : p(𝔭_m) ⊂ [O,ω)}` is clopen.

## Imported statements

1. **Relations (rel1)** of the rank-two Cuntz–Krieger algebra `𝒜`:
   - `s_{u,v}^* = s_{v,u}`;
   - `s_{u,v}s_{v,w} = s_{u,w}`;
   - `s_{u,v} = Σ_{w∈W, σ(w)=e_j, o(w)=t(u)=t(v)} s_{uw,vw}` for `j = 1, 2`;
   - `s_{u,u}s_{v,v} = 0` for distinct `u,v ∈ W̄_0`.
   - Lemma `f2`: for all `m`, `s_{u,v} = Σ_{w∈W, σ(w)=m, o(w)=t(u)} s_{uw,vw}`.
   - Lemma `5`: `s_{u,u}s_{v,v} = 0` if `σ(u) = σ(v)` and `u ≠ v`.
   - Corollary `4`: `ūv = (d,uv)` exists whenever `t(ū) = o(v)`.
2. **φ on generators.** For `w̄_1, w̄_2 ∈ W̄` with `t(w̄_1) = t(w̄_2)`, put
   `p_i = ᾱ^{-1}(w̄_i)`, and let `γ` be the unique element with `γt(p_1) = t(p_2)`. Then
   `φ(s_{w̄_2,w̄_1}) = γ1_{Ω(p_1)} = 1_{Ω(p_2)}γ` defines a *-homomorphism
   `φ: 𝒜 -> C(Ω)⋊Γ`.
3. **Lemma c1.** `1 = Σ_{p∈𝔚̄_m} 1_{Ω(p)}` for every `m`.
4. **Lemma c2.** The sets `Ω(p)`, `p ∈ 𝔚̄`, form a basis of the topology of `Ω`.
5. **Proof of main2.**
   - `1_{Ω(p)} = φ(s_{w̄,w̄})` with `w̄ = ᾱ(p)`.
   - For `γ ∈ Γ` and `m` with `d(O,γ^{-1}O) ≤ m_1, m_2`: each `p ∈ 𝔚̄_m` has
     `p' ∈ 𝔚̄` with `γt(p) = t(p')`, hence `γ1_{Ω(p)} = φ(s_{ᾱ(p'),ᾱ(p)})`.
6. **Remark after main2.**
   - `C(Ω)⋊Γ` is simple, nuclear and purely infinite.
   - It is isomorphic to the reduced crossed product `C(Ω)⋊_rΓ`.
7. **Examples.** When `B` is the building of `PGL_3(K)`, with `K` nonarchimedean of
   characteristic zero and `Γ` a lattice, (H2) holds as well as (H0), (H1), (H3). "There
   are several concrete examples in [CMSZ] where all these hypotheses are satisfied."

Source: G. Robertson, T. Steger, *Affine buildings, tiling systems and higher rank
Cuntz–Krieger algebras*, J. reine angew. Math. 513 (1999), 115–144, arXiv:1302.5593.
