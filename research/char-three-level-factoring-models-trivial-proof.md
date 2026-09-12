---
rg: 2
id: char-three-level-factoring-models-trivial-proof
kind: route
title: Central relator errors turn a displaced level-factoring model into an embedding of G_3 or PG in an ultraproduct of finite groups
target: char-three-level-factoring-models-of-leavitt-units-are-trivial
requires:
  - ternary-leavitt-rank-models-move-z-iff-nontrivial
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - d-ary-leavitt-groups-nonsofic-over-finite-fields
  - projective-leavitt-unit-groups-mod-scalars-are-nonsofic
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md
---

Section 1 of the artifact: Lemmas 1.1–1.3, Theorem 1.4 and Corollary 1.5.

1. **Injectivity.** If `σ` is nontrivial, `σ∘ι` is injective
   (`ternary-leavitt-rank-models-move-z-iff-nontrivial`). It factors with the same `π_k`.
2. **Central errors.** For `g, h` in a finite set, `e_k = τ_k(gh)^(−1) τ_k(g) τ_k(h)` has
   `rk(π_k(e_k) − 1) = o(n_k)`.
   - A non-central `e_k` costs at least `d_k n_k/4` (Lemma 1.3).
   - So `e_k = ±1` for `ω`-almost all `k`.
3. **Ultraproduct of finite groups.** Modulo `±1`, the maps form a homomorphism
   `Φ : G -> prod_ω PGL_(m_k)(F_3)`.
   - If `Φ(w) = 1`, then `σ(w)` is a limit of images of scalars, so it commutes with `σ(G)` and `w` is
     central.
   - The centre of `G` is `<z>`, because `PG` is simple (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`).
4. **Contradiction.** `G/ker Φ` is `G` or `PG`. It embeds in an algebraic ultraproduct of finite groups,
   hence is sofic. That contradicts `d-ary-leavitt-groups-nonsofic-over-finite-fields` and
   `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`.

*Verification by `w3-vf-linear` (2026-09-12), Section 21.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS, conditional on simplicity of PG and nonsoficity of G and PG. Recomputed: Lemma 1.3 over F_3 ([x,u] = 1 + A − B, [1+N,u''] = 1 + Nw⊗chi); central errors ±1; ker Phi inside Z(G) = <z> by injectivity of sigma∘iota; and algebraic ultraproduct ⟹ LEF ⟹ sofic.*
