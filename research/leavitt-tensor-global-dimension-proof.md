---
rg: 2
id: leavitt-tensor-global-dimension-proof
kind: route
title: Resolve the second factor as a bimodule and induct on the number of Leavitt factors
target: leavitt-tensor-global-dimension-bound
requires:
  - leavitt-algebra-hochschild-dimension-at-most-one
---

**Step 1 (Eilenberg--Rosenberg--Zelinsky inequality).** Let `A, C` be
`k`-algebras with `n = pd_(C^e) C`, and let `M` be a left `A ⊗_k C`-module.
- Take a projective bimodule resolution `0 -> Q_n -> ... -> Q_0 -> C -> 0`. It
  splits as right `C`-modules, so `Q_• ⊗_C M -> M` is exact.
- Each `Q_i` is a summand of a free bimodule, and
  `(C ⊗_k C) ⊗_C M = C ⊗_k M`. Tensoring a projective resolution of `M` over
  `A` with `C` over the field `k` gives `pd_(A ⊗ C)(C ⊗_k M) <= pd_A M`.
- Dimension shifting then gives `pd_(A ⊗ C) M <= l.gl.dim A + n`.

**Step 2 (upper bound).** By `leavitt-algebra-hochschild-dimension-at-most-one`,
`n <= 1` for `C = L`. Apply Step 1 `d` times, with `A = B ⊗ L^(⊗(j-1))`.
Right modules: apply the argument to opposite algebras, using the involution
`x_i <-> x_i^*` to identify `L^op` with `L`.

**Step 3 (lower bound, import).** Ara--Cortiñas arXiv:1108.0352v3, Example 5.2,
read from the PDF text on MSI on 2026-09-12:
- `l.gl.dim L_2 <= 1` (their [9], Theorem 3.3);
- "if k is a field and R and S are k-algebras, then
  l.gl.dim R + w.gl.dim S <= l.gl.dim(R ⊗_k S)" (Cartan--Eilenberg XI.3.1);
- `w.gl.dim L_2 > 0`.

So `w.gl.dim L = 1`, and induction gives `l.gl.dim L^(⊗d) >= d`. With Step 2,
equality holds.
