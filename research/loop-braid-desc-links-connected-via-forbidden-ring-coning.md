---
rg: 2
id: loop-braid-desc-links-connected-via-forbidden-ring-coning
kind: route
title: "L_n(LB_*) is ⌊(n−5)/3⌋-connected: forbidden-ring family, link lemma, Morse filtration by ring use, and the coning statement"
target: loop-braid-descending-links-are-increasingly-connected
requires:
  - loop-braid-forbidden-ring-coning-statement
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
  - ordered-matching-complex-kn-simply-connected-n-ge-8
artifacts:
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
---

The full proof is artifact §§1–4. Put `η(N) = ⌊(N − 5)/3⌋`.

1. **Family.** For `F ⊂ [n]`, `X_n(F) := t^{-1}(OM(K_{[n]∖F}))`.
   - This is a P-invariant full subcomplex with strict fundamental domain `Q_F`.
   - Its stabilizers are the cabling subgroups (colimit claim, step 1).
2. **Link Lemma (artifact Lemma 2.1).** For an m-simplex σ,
   `lk_{X_n(F)}(σ) ≅ X_{n−m}(F' ∪ Fus_σ)`, with free count `N − 2m`, respecting types.
   - Proof: the link is `P_σ · lk_Q(σ)`, the development of `lk_Q σ ≅ Q_{n−m}(Fus)` with groups
     `P_{σ∪τ} = (P'_{τ̄})κ_Γ`. This uses injectivity and composition of cabling maps.
3. **Base cases (artifact Lemmas 3.1, 3.2).** `X_n(F)` is connected for `N ≥ 5` and simply
   connected for `N ≥ 8`.
   - Rerun the McCool/(C1)/(C3) colimit argument over `Q_F`. All bounds depend only on N.
   - Use `ordered-matching-complex-kn-simply-connected-n-ge-8` for `Q_F ≅ OM(K_N)`.
   - Apply the covering criterion.
4. **Morse step (artifact §4.1).**
   - Let `q ∈ {0, 1, 2, 3}` record whether a vertex's type uses v, w, or both.
   - Add `q = 3`, then `q = 1`, then `q = 2`, on top of `X_n(F ∪ {v, w})`.
   - By step 2, the descending links are family members of free count `N − 2`, `N − 3`, `N − 2`
     respectively.
   - So `(X_n(F), Y_n(F; v, w))` is `(min(c(N−2), c(N−3)) + 1)`-connected.
5. **Induction (artifact Thm 4.3).**
   - Base: `N ≤ 10` is step 3.
   - For `N ≥ 11`: by induction, `(X_n(F), Y)` is `η(N)`-connected. Then
     `loop-braid-forbidden-ring-coning-statement` gives `π_j(Y) = 0` for `j ≤ η(N)`, hence
     `π_j(X_n(F)) = 0`.
6. **Conclusion.** Take `F = ∅`: `L_n(LB_*)` is `⌊(n − 5)/3⌋`-connected, which tends to infinity.
