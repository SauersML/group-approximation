---
rg: 2
id: self-similar-ring-elementary-groups-non-uniform-growth
kind: claim
title: If a finitely generated ring R of characteristic 2 satisfies R ≅ M_2(R) and EL_n(R) is infinite (n ≥ 3), then EL_n(R) is a Kazhdan group of non-uniform exponential growth
artifacts:
  - research/artifacts/sk-verify-14-2026-09-13-part4.md
---

**ESTABLISHED (unreviewed; sk-free-8).** Let `R` be a unital ring of characteristic 2, generated as a ring by a finite set `Σ`, with `R ≅ M_2(R)` as rings. Let `n ≥ 3`. Then `inf_S ω(EL_n(R), S) = 1`, where `ω(G,S) = lim_ℓ |B_S(ℓ)|^(1/ℓ)`. If `EL_n(R)` is infinite, it has property (T) and exponential growth, so it has **non-uniform exponential growth** in Gromov's sense.

**Examples.**
- `R_X = LC(X,F_2) ⋊ Z` for a constant-length-2 substitution subshift: `substitution-subshift-elementary-groups-non-uniform-growth`.
- The binary Leavitt algebra: `nonsofic-leavitt-el4-non-uniform-exponential-growth`.

Route: `self-similar-ring-elementary-groups-non-uniform-growth-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived: Lemma 4 (`EL_n(M_N(S)) = EL_(nN)(S)`), the scale isomorphisms `EL_n(R) ≅ EL_(X_k × [n])(R)`, generating sets `U_k` with `k`-independent constants, `ω(EL_n(R), U_k) ≤ exp(C(r_k/3)^(β−1)) → 1`, and exponential growth from (T) and non-amenability. See `research/artifacts/sk-verify-14-2026-09-13-part4.md` §3.
