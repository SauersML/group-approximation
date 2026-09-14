---
rg: 2
id: minimal-cantor-crossed-products-stabilize-laurent-pairs-proof
kind: route
title: Blockwise invertible lifts of the residue map of a, chosen per tower type, give a unit of a tower algebra congruent to a modulo q
target: minimal-cantor-crossed-products-stabilize-laurent-pairs
requires: [laurent-right-ideals-of-cantor-crossed-products-columnwise]
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part1.md
---

Notation as in `laurent-right-ideals-of-cantor-crossed-products-columnwise`: `q = u^αq_0`, `q_0(0) ≠ 0`, `d = deg q_0`, `A_q = F[u]/(q_0)`, and `ρ_q : V → A_q`, `δ_t ↦ ū^t`.

1. **Residues.** Let `ar + qs = 1` and let `w_r` be the propagation of `r`. The columns of `qs` lie in `qV`, so `ρ_q∘a∘r = ρ_q` as maps `V → A_q`. For `a = Σ_jf_ju^j`, `ρ_q(aδ_n) = Σ_jf_j(T^{n+j}x)ū^{n+j} = ū^nτ(T^nx)` with `τ(ξ) = Σ_jf_j(T^jξ)ū^j`, a locally constant map `X → A_q`.
2. **Towers.** Choose a Kakutani–Rokhlin partition `𝒫` with heights `h ≥ 2w_r + d + 2`, refined so that each base atom determines `τ(T^iξ)` for `0 ≤ i < h`.
3. **Surjections.** For an occurrence `[b,b+h)` define `φ_0(δ_i) = ū^i` and `ψ_0(δ_i) = ū^iτ(T^{b+i}x)`, maps `F^h → A_q`.
   - `φ_0` is onto, since `h ≥ d`.
   - `ψ_0` is onto. For `m` at distance `> w_r` from both ends of the occurrence, `ū^m = ρ_q(δ_m) = ρ_q(arδ_m) = Σ_n r(n,m)ρ_q(aδ_n)`, and every `n` with `r(n,m) ≠ 0` lies in the occurrence. So `ū^{m−b} ∈ im ψ_0` for at least `d` consecutive `m`, and these span `A_q`.
   - `ψ_0` depends only on the base atom.
4. **Block unit.** Two surjections `F^h → A_q` differ by an automorphism. Choose any isomorphism `ker ψ_0 → ker φ_0`, and on a complement `C_ψ` of `ker ψ_0` use `(φ_0|_{C_φ})^{−1}∘ψ_0|_{C_ψ}` into a complement `C_φ` of `ker φ_0`. This gives `G ∈ GL_h(F)` with `φ_0∘G = ψ_0`, chosen per base atom.
5. **Global unit.** `g = Σ_aΣ_{i,i′}G_a(i′,i)e_{T^{i′}B_a}u^{i′−i}` lies in `GL_1(A_𝒫) ⊆ R^×`, with inverse the block matrices `G_a^{−1}`. For `t = b+i`, `ρ_q(gδ_t) = ū^bφ_0(Gδ_i) = ū^bψ_0(δ_i) = ρ_q(aδ_t)`.
6. **Conclude.** Every column of `g − a` lies in `qV`, so by the lemma `g − a = qc` with `c ∈ R`. Then `a + qc = g ∈ R^×`. ∎

**Corollary (rows).** If `(p_1,…,p_n)` is unimodular over `F[u^{±1}]`, put `q = Σ_{i≥2}p_iλ_i = gcd(p_2,…,p_n)`. Then `p_1R + qR = R`, so `p_1 + qc ∈ R^×`, i.e. `p_1 + Σ_ip_i(λ_ic) ∈ R^×`.

**Model test.** For the one-point system `R = F_2[u^{±1}]`, step 2 fails: there are no towers. The pair `(1+u, Φ_5(u))` is not stable there, because `1+ū` is not a power of `ū` in `F_16`.
