---
rg: 2
id: linear-coset-shift-periodic-density-iff-separable-proof
kind: route
title: Direct proof that coset-shift periodic density is separability
target: linear-coset-shift-periodic-density-iff-separable
requires: []
artifacts:
  - research/artifacts/primitive-shift-goodness-dictionary-2026-09-18.md
---

## Why sufficient

This is a complete elementary proof. Full details are in §5 of the artifact.

1. **Structure.** A configuration `c` lies in `X_K` exactly when it is constant on left
   `K`-cosets. Since `K = <k_1, ..., k_r>`, it suffices to impose `c(g k_i) = c(g)`, which
   is a local linear rule. Left translation preserves right-coset-constancy, so `X_K` is
   shift-invariant.
2. **(⇐) Separable implies dense.**
   - Let `c ∈ X_K` and let `W` be finite. Separability gives `K = ∩ KN` over finite-index
     normal `N`, so we can choose one `N` with `w^{-1}w' ∉ KN` whenever `w, w' ∈ W` and
     `wK ≠ w'K`.
   - Define `c'` to be `c(w)` on `NwK` and `0` elsewhere. It is well defined, because
     `NwK = Nw'K` exactly when `w^{-1}w' ∈ KN`.
   - `c'` is right `K`-invariant and left `N`-invariant, so it is a periodic point of
     `X_K`, and it agrees with `c` on `W`.
3. **(⇒) Dense implies separable.**
   - Let `g ∉ K`. The indicator `1_K` lies in `X_K`.
   - A periodic `c' ∈ X_K` agreeing with `1_K` on `{1, g}` is left invariant under a
     finite-index normal subgroup `N`. So `c' = 1` on `NK`, while `c'(g) = 0`.
   - Hence the finite-index subgroup `NK ⊇ K` excludes `g`.
4. **LERF.** Apply item 2 of the claim to every finitely generated `K`, with `B = F_p`.

No external result is used.
