# sk-verify-18 part 8: outer automorphisms and corner subfactors of L(G_X) (2026-09-14)

Queue lines 18–20, sk-vn-rigidity, `research/artifacts/sk-vn-rigidity-2026-09-14.md` §§1–2:
- `subshift-group-factor-out-contains-z` (V1), route `subshift-group-factor-out-contains-z-proof`;
- `subshift-group-unitary-embeddings-are-corner-subfactors` (V2), route `subshift-group-unitary-embeddings-are-corner-subfactors-proof`;
- import `icc-group-out-injects-into-group-factor-out`, citation route of the same name.

None carried a sk-verify-19 review line at review time.

## Verdicts
- **V1: PASS**, re-derived. It is conditional on the reviewed inputs its route requires: `subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy` (sk-verify-16 PASS), `simple-kazhdan-lef-group-from-minimal-subshift`, and the import below. The countability of Out for property (T) factors is recalled (Connes), not source-checked and not used for (1)–(2).
- **V2: PASS**, re-derived. It is conditional on `subshift-elementary-groups-are-character-rigid` (PASS by sk-characters-rigidity-a and sk-verify-8) and `separable-factors-hold-countably-many-subshift-groups` (sk-verify-10 PASS).
- **Import: PASS at source.** Chifan–Ioana–Osin–Sun II, arXiv:2304.07457 e-print `main.tex`, read on MSI 2026-09-14. l.2048 `\begin{prop}\label{inj} If $G$ is ICC, then $\overline{\Psi}$ is injective.`, where Ψ̄: Char(G) ⋊ Out(G) → Out(L(G)), (ρ,δ) ↦ [u_g ↦ ρ(g)u_{δ(g)}]. The l.220 remark matches too.

No FAIL, no GAP.

## V1 re-derived
- **Step 1.** d_k e_ij(r) d_k⁻¹ = e_ij(a_i r a_j⁻¹) with a = (u^k,1,1). So θ_k = Ad(d_k) preserves G, and θ_kθ_l = θ_{k+l}.
- **Step 2.**
  - Commuting with every e_ij(1) forces g = cI_3. Commuting with every e_ij(r) makes c central.
  - Z(R) = F_2: rf = fr gives f_k(f∘T⁻ᵏ − f) = 0, and aperiodicity kills f_k for k ≠ 0. ru = ur makes f_0 T-invariant, hence constant.
  - So C_{GL_3(R)}(G) = {I}.
- **Step 3.** If θ_k = Ad(h)|_G with h ∈ G, then h⁻¹d_k centralizes G, so d_k = h ∈ G. But ind(d_k) = −k, and ind vanishes on E_3(R). So k ↦ [θ_k] is an injective homomorphism Z → Out(G_X).
- **Step 4 (ICC).** For g ≠ e, C(g) is proper because Z(G) = 1. A finite class would make C(g) of finite index, and its normal core would be a proper normal subgroup of finite index, hence infinite and nontrivial. That contradicts simplicity.
- **Step 5.** With ρ = 1, CIOS `inj` gives Out(G) ↪ Out(L(G)).
- **Re-derived from source.**
  - Ad(u)(u_g) = u_{δ(g)} gives c_h = c_{δ(g)hg⁻¹}.
  - Σ|c_h|² = 1 forces a finite twisted class, so there is a finite-index G_h with δ = Ad(h) on G_h.
  - For h_1, h_2 in the support, h_2⁻¹h_1 centralizes a finite-index subgroup, so ICC gives u = c_h u_h, and δ is inner.

## V2 re-derived
- **Step 1.** φ = τ∘ι is normalized, positive definite and a class function, since τ is tracial. By character rigidity φ = c·1 + (1−c)δ_e. If c = 1, ‖ι(g)−1‖₂² = 2 − 2Re τ(ι(g)) = 0, so ι is trivial.
- **Step 2.**
  - span ι(G) is ‖·‖₂-dense in N = ι(G)'', so L²(N,τ) is the GNS space of φ.
  - The GNS representation of c·1 + (1−c)δ_e is π_0 ⊕ λ. These are disjoint, because λ has no invariant vectors for infinite G.
  - The isotypic projection is central in π(G)', hence in Z(N). So there is z ∈ Z(N) with ι(g)(1−z) = 1−z, and Nz ≅ λ(G)'' through ι(g)z ↦ λ_g.
  - Trace scaling: for g ≠ e, τ(ι(g)z) = (1−c)⟨λ_gδ_e,δ_e⟩ = 0. With τ(ι(g)) = c this gives τ(1−z) = c and τ(ι(g)z) = (1−c)δ_e(g).
- **Step 3.** (⇐): ι(g) = (1−z) + v_g is an injective homomorphism into U(M).
- **Step 4.** A corner copy gives G_X ≤ U(M). For a separable II_1 factor and a fixed alphabet, only countably many X occur, by the reviewed count.
- **Model tests re-checked.**
  - M = ℂ: G_X is perfect, so only the trivial ι, with c = 1.
  - ι = λ: c = 0, z = 1.
  - λ ⊕ 1 in L(G_X) ⊕ ℂ: c = 1/2.

## Notes (0 lines)
- The character rigidity node's title says "extreme characters", while its body and route prove the full simplex c·1 + (1−c)δ_e. V2 uses the full form, which is what that node's reviews passed.
- The artifact's commensurability observation (infinite simple groups have no proper finite-index subgroups, so commensurability is isomorphism) is correct. The Zhou 2026 counterexample and the philarchive note are recorded as web-only, and are not relied on.
