---
rg: 2
id: irreducible-sft-leavitt-gl-max-mf-quotient-formula
kind: claim
title: For a purely infinite simple Leavitt path algebra of a finite graph, the maximal MF quotient of GL_n is coker(1 - N^t) tensor k^x plus ker(1 - N^t), at every rank
distinct_from:
  purely-infinite-steinberg-gl-max-mf-quotient-is-k1: that identifies the maximal MF quotient with K_1 for every locally compressible minimal groupoid; this computes it explicitly for finite graphs from the incidence matrix
  abc-leavitt-path-k-theory-exact-sequence: that is the K-theory computation; this is its consequence for the approximation theory of general linear groups
artifacts:
  - research/artifacts/un-k1-homology-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route `irreducible-sft-leavitt-gl-max-mf-quotient-formula-proof`.

**Setting.**
- `E` is a finite graph with no sinks, cofinal (every vertex connects to every cycle), and satisfying
  condition (L).
- `N = N_E` is its incidence matrix and `k` is a countable field.

**Claim.** For every `n >= 1`, every homomorphism from `GL_n(L_k(E))` to an MF group factors through
`κ_n`, and

`GL_n(L_k(E)) / Rad_MF(GL_n(L_k(E))) ≅ K_1(L_k(E)) ≅ (Coker(1 − N^t | ℤ^(E^0)) ⊗ k^×) ⊕ Ker(1 − N^t | ℤ^(E^0))`,

with `Rad_MF = [GL_n, GL_n]`. The same holds for the unit group `L_k(E)^×`.

**Remark: homological reading (NOT established by the route; one input is recalled).** Suppose `E` is the graph of an irreducible, non-permutation 0–1 matrix `A`, so that
`N = A` and `L_k(E) = A_k(G_A)` for the one-sided SFT groupoid `G_A`. Matui's `CKHomology`
(`matui-sft-groupoid-homology-is-k-theory`) together with Cuntz's `K_0(O_A) = Coker(1 − A^t)`,
`K_1(O_A) = Ker(1 − A^t)` (recalled, not imported) gives

`maximal MF quotient of GL_n(A_k(G_A)) ≅ (H_0(G_A) ⊗ k^×) ⊕ H_1(G_A)`.

So on the paradox side, MF approximation of `GL_n` detects exactly the groupoid homology in degrees 0 and 1,
with `H_0` weighted by `k^×`.

**Calibrations.**
- **The rose `R_d`.** `N = (d)` and `1 − N^t = 1 − d`, so `Coker = ℤ/(d−1)` and `Ker = 0`. The quotient is
  `ℤ/(d−1) ⊗ k^× = k^×/(k^×)^(d−1)`. This is `non_mf_groups_exist.tex` Cor l.1297, and for `d = 2` it is 0.
- **`E` the 2-cycle with one extra loop** (`N = [[1,1],[1,0]]`). `1 − N^t = [[0,−1],[−1,1]]` has determinant −1,
  so both terms vanish. The unit group `L_k(E)^×` is perfect with no nontrivial MF quotient, for every field
  `k`.
- **`N = [[2,1],[1,2]]`.** `1 − N^t = [[−1,−1],[−1,−1]]`, with `Coker ≅ ℤ` and `Ker ≅ ℤ`. The quotient is
  `k^× ⊕ ℤ`, so these unit groups have infinite MF quotients.

**Review (un-verify, 2026-09-13): PASS.** Abrams–Aranda Pino criterion for finite cofinal sink-free (L) graphs, the canonical `K_1` classification, Ara–Brustenga–Cortiñas Corollary 7.7, and the tensor form; calibrations recomputed: rose `ℤ/(d−1) ⊗ k^×`, `[[1,1],[1,0]]` with `det(1−N^t) = −1`, `[[2,1],[1,2]]` with Smith form `diag(1,0)` giving `k^× ⊕ ℤ`. The homological remark is correctly marked not established. See `research/artifacts/un-review-2026-09-13-part9.md` §3.
