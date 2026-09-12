---
rg: 2
id: leavitt-two-root-defect-piece-rank-model-proof
kind: route
title: Restrict to the invariant defect corner, and kill the fixed case with globality, a quotient model and perfection
target: leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model
requires:
  - two-root-identity-is-corner-local-for-leavitt-rank-models
  - leavitt-rank-models-kazhdan-fixed-ideals-are-global
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/two-root-defect-piece-and-fd-representations-2026-09-12.md
  - research/artifacts/rank-row-compression-audit-2026-09-12.md
---

Artifact Section 1, Theorem 1.2 and Corollary 1.3.

1. **Invariant corner.** The pair on `[1000]` commutes with `Gamma`, so `P` commutes with
   `sigma(Gamma)` and `PM = qM` is invariant. For an invariant idempotent,
   `sigma(gamma) q = q sigma(gamma) q`, so `q sigma(.) q` is a homomorphism on `Gamma`.
2. **Fixed case.** If it is trivial, `qM` lies in `Fix_r(sigma(Gamma))`
   (Lemma 1 of the audit artifact). That equals `Fix_r(sigma(R^x)) = fM`
   (`leavitt-rank-models-kazhdan-fixed-ideals-are-global`, degree `(1,0)`).
3. **Quotient model.** `(1-f) sigma (1-f)` is a homomorphism because `fM` is invariant. Its corner
   product is `(1-f) P (1-f) = 0`, because `N'_23 f = 0` and `P = fP`. Corner locality
   (`two-root-identity-is-corner-local-for-leavitt-rank-models`) makes the quotient model trivial.
4. **Perfection.** `sigma(g) - 1` then lies in `fM(1-f)`, a square-zero bimodule, so `sigma` lands
   in an abelian group. `R^x` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`), so
   `sigma` is trivial, a contradiction.
5. **Injectivity and corner products.** The restricted model is nontrivial, hence injective on
   `iota_0(R^x)` (`binary-leavitt-unit-group-is-simple`). Since `iota_0 o iota_P' = iota_(0P')`,
   its corner products are `q N^(0P')_23 N^(0P')_12 q`, which corner locality makes nonzero. A
   conjugating compressor then has `q sigma(u) q != 0`, because `P = qP`.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 52 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS. `Gamma = iota_0(R^x)` equals the nine-leaf `EL_alpha(R)` as a set, so globality applies in degree `(1,0)`. The assigned verifier remains `w3-vf-linear`.*

*Verification by `w3-vf-linear` (2026-09-12), Section 10.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed Lemma 1.1, the quotient model (1−f)σ(1−f) and its vanishing corner product, the square-zero abelian rest, ι_0∘ι_P' = ι_(0P'), and Corollary 1.3. Globality, corner locality, perfection and simplicity are cited. Not decision-level.*
