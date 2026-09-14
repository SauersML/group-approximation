---
rg: 2
id: subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology
kind: claim
title: The simple Kazhdan groups EL_n(LC(X,F_2)⋊Z) have vanishing ℓ²-Betti numbers and bounded cohomology with mixing coefficients, and fail property (CS)
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift and `n ≥ 3`. Put `G = EL_n(LC(X,F_2) ⋊_T Z)`; over `F_q`,
use `EL_n/Z`. Then:
1. `β_k^{(2)}(G) = 0` for every `k ≥ 0`.
2. `H_b^k(G,E) = 0` for every `k ≥ 0` and every mixing coefficient module `E`, for example `E = ℓ^p(G)`, `1 ≤ p < ∞`.
3. `G` does not have the Connes–Sullivan property (CS) of Breuillard–Kalantar–Kennedy–Ozawa.

So neither of the BKKO routes to C*-simplicity decides `subshift-elementary-groups-are-cstar-simple`: the vanishing criteria
(non-trivial bounded cohomology or ℓ²-Betti numbers) and property (CS) are both unavailable.

**Proof:** `subshift-el-groups-vanishing-l2-bounded-cohomology-proof`.

**Review (sk-verify-13, 2026-09-13, `research/artifacts/sk-verify-13-2026-09-13-part5.md` §2):** PASS.
- Items 1–2: the BKKO propositions were re-checked verbatim against the arXiv:1410.2518 source on MSI (l.626–627 and l.643–649).
- Item 3: re-derived against BKKO's definition of (CS) (l.939–941, "π^{-1}(U) ⊂ R_a(G)").
  - The quasi-regular representation `λ_{G/S_y}` is weakly regular, and `R_a(G) = 1` since `G` is simple and non-amenable.
  - A basic SOT neighbourhood is approximated through finitely supported vectors.
  - `⋂ s_iS_ys_i^{-1}` fixes their cosets, so `π^{-1}(U)` is infinite.
- Conditional on `cut-stabilizers-of-el-n-are-locally-finite-normalish` (PASS, same artifact).
