---
rg: 2
id: unipotent-valued-rank-models-proof
kind: route
title: Torsion of invertible order is exactly rank-rigid for unipotents, and one such element normally generates EL_3
target: unipotent-valued-rank-models-of-el3-are-trivial
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-extensions-2026-09-12.md
---

Artifact Section 4.1.

1. **Lemma 3.** `x^m - 1 = N c` with `N = x - 1` and `c = m + sum_(l>=2) binom(m,l) N^(l-1)`.
   `c` is invertible because `m` is invertible and `N` is nilpotent. So `rk(x^m - 1) = rk(N)` at
   every finite stage, and a unipotent `g` with `g^m = 1` in `M` is `1`.
2. **`char k != p`.** `x_12(1)` has order `p`, so its image is `1`. Weyl conjugation gives
   `sigma(x_kl(1)) = 1` for all `k != l`.
3. **`char k = p`.** `h` has order 3 (`p = 2`) or 2 (`p` odd), is not central in
   `SL_3(F_p) = EL_3(F_p)`, and maps to `EL_3(R)` through `F_p -> R`. Its image is `1`, so the
   kernel of `SL_3(F_p) -> M^x` is normal and contains a non-central element. Simplicity of
   `PSL_3(F_p)` and perfection of `SL_3(F_p)` make that kernel everything, so
   `sigma(x_kl(1)) = 1`.
4. **All roots.** `x_ik(a) = [x_ij(a), x_jk(1)]` gives `sigma(x_ik(a)) = 1`, and root elements
   generate `EL_3(R)`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 38 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
