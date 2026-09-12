---
rg: 2
id: char-three-level-factoring-models-of-leavitt-units-are-trivial
kind: claim
title: Characteristic-three rank models of the ternary Leavitt unit group that factor through general linear groups with positive transvection displacement are trivial
distinct_from:
  transvection-displacement-forces-exact-local-embedding: that is characteristic two for R^x, and its odd-characteristic remark confines relator errors to the centre but leaves central errors standing for G_3; this is characteristic three for G_3 and PG, where central errors are fatal through the centre of G_3 and the nonsoficity of G_3 and PG.
  ternary-leavitt-units-have-a-nontrivial-char-three-rank-model: that is the open gate; this excludes one architecture for its yes direction and settles nothing else.
artifacts:
  - research/artifacts/char-three-level-factoring-and-hnn-models-2026-09-12.md
---

**ESTABLISHED** (proof: Section 1 of the linked artifact, route
`char-three-level-factoring-models-trivial-proof`).

**Theorem.** Let `G = L_(F_3)(1,2)^x`, and let `σ = lim_ω π_k ∘ τ_k : G -> M^x` be a characteristic-three
rank model, where:
- `τ_k : G -> GL_(m_k)(F_3)` are set maps with `m_k >= 4`;
- `π_k` are representations of dimension `n_k`.

If the transvection displacement `d_k = rk(π_k(t) − 1)/n_k` has `lim_ω d_k > 0`, then `σ` is trivial.
The same holds for models of `PG = G/{±1}`.

**Proof sketch.**
1. A nontrivial `σ` becomes injective along the corner embedding, keeping the same `π_k`.
2. A non-central relator error costs at least `d_k/4`, because two commutators with transvections reach a
   transvection. So relator errors are `±1`.
3. Reducing modulo `±1` gives a homomorphism `G -> prod_ω PGL_(m_k)(F_3)` whose kernel lies in the centre
   `<z>`. So `G` or `PG` embeds in an algebraic ultraproduct of finite groups and is sofic. Both are
   nonsofic.

**Excluded architectures** (artifact Corollary 1.5), for `G_3` and `PG`:
- natural level assignments that send one fixed element with nontrivial image to a transvection;
- level-factoring models with projective share bounded below: Steinberg modules, projective
  indecomposables, and free and twisted regular modules;
- central relator errors, which the characteristic-two artifact left open over `F_3`.

**Survivors.** Either the displacement `d_k -> 0` at the factoring level, or the model does not factor
through the level groups at all. In particular, take a model of the level unit group `L` that is
level-factoring with positive displacement. It extends to all of `G` only if some element of `G` is sent
to positive rank distance from the image of the level representation.

## Attempts

Established; see `char-three-level-factoring-models-trivial-proof`.
