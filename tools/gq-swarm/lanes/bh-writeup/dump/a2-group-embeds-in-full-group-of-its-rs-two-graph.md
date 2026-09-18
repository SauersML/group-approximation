---
rg: 2
id: a2-group-embeds-in-full-group-of-its-rs-two-graph
kind: claim
title: A type rotating group acting freely on the vertices of an Ã₂ building embeds in the topological full group of its Robertson–Steger 2-graph groupoid
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**ESTABLISHED** (2026-09-18) by `a2-group-embeds-in-rs-two-graph-geometric-proof`. That is
a lane proof and has not been independently reviewed.

Let `Γ` and `Λ_Γ` be as in `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic`.
Claim: there is an injective homomorphism `Γ -> [[G_{Λ_Γ}]]` whose elements act on
`Λ_Γ^∞ ⊇ Y ≅ Ω` as `Γ` acts on the boundary.
- `Y` is the clopen union of the vertex cylinders `Z(δ(d))`, `d ∈ D`. It equals
  `Λ_Γ^∞` when `Γ` is vertex-transitive.
- The homomorphism is the identity off `Y`.
- Each element is a finite cylinder exchange `Z(u) -> Z(u')`. So the image lies in the
  cylinder-exchange group `[[Λ_Γ]]` of `brick-coded-two-graph-full-groups-embed-in-brin-thompson`.

**How the proof works.** It uses sector geometry only: Robertson–Steger Lemmas `oalpha`,
`c1`, `c2`, `c3` and Corollary `9B`, read at source (arXiv:1302.5593, §7), together with
(H1) and standard building facts.
- It does not use `φ`, simplicity of `𝒜`, (H2), (H3), Kumjian–Pask or Renault.
- So it covers every locally finite thick Ã₂ building, exotic ones included.
- For `PGL_3(K)` lattices, the same conclusion follows from `φ` and simplicity in
  `rank-two-prefix-replacement-groups-contain-infinite-kazhdan`.
- The missing pins listed below are no longer needed.

**Earlier sketch (superseded; kept for the record).**
1. Robertson–Steger, Theorem `main2`: `φ: 𝒜 -> C(Ω) ⋊ Γ` is an isomorphism with
   `1_{Ω(p)} = φ(s_{w̄,w̄})` (pinned in `robertson-steger-a2-boundary-algebras-are-rank-two-ck`).
   So `φ` carries the canonical diagonal of `𝒜` onto `C(Ω)`.
2. `𝒜 ≅ C*(Λ_Γ) = C*(G_{Λ_Γ})` with the diagonal going to `C(Λ_Γ^∞)`, sending
   `s_{u,v}` to `s_u s_v^*`. Recalled from Kumjian–Pask, not pinned.
3. `C(Ω)` is a Cartan subalgebra of `C(Ω) ⋊ Γ` when the action is topologically free. By
   Renault's reconstruction for effective étale groupoids, a unitary normalizer of the
   diagonal is supported on a global compact open bisection, which gives an element of
   `[[G_{Λ_Γ}]]` acting as `Ad` of the normalizer on the spectrum. Not pinned.
4. `γ ↦ φ^{-1}(u_γ)` is a normalizer, and `Γ` acts faithfully on `Ω`, so the resulting
   homomorphism into `[[G_{Λ_Γ}]]` is injective. Faithfulness and topological freeness of
   the boundary action are not pinned here.

**Missing pins of the superseded sketch (not needed by the proof).** Kumjian–Pask's identification of Robertson–Steger algebras as 2-graph
algebras; Renault, *Cartan subalgebras in C*-algebras*, arXiv:0803.2284 (fetched on MSI,
theorem not yet located in the TeX); topological freeness of `Γ ↷ Ω`.
