---
rg: 2
id: loop-braid-desc-links-connected-via-bfmwz-push
kind: route
title: "L_n(LB_*) is ⌊(n−5)/3⌋-connected: Morse step to X_n(F∪{v,w}), BFMWZ simplexwise-injective reduction, pair-twist pushes with controlled mutual links, and a push complexity"
target: loop-braid-descending-links-are-increasingly-connected
requires:
  - loop-braid-push-complexity-statement
  - loop-braid-pair-twist-push-mutual-link
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
  - ordered-matching-complex-kn-simply-connected-n-ge-8
artifacts:
  - research/artifacts/zp-loop-braid-bfmwz-push-decomposition-2026-09-17.md
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
---

The full proof is artifact §§3–4 (Lemma 3.1, Thm 4.2). It reuses the w8 Link Lemma, base cases and
Morse step (artifact `zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md`, Lemma 2.1,
Lemmas 3.1–3.2, (4.1)), which rest on the last two prerequisites. Put `η(N) = ⌊(N − 5)/3⌋`.

Imported (BFMWZ, *The braided Ptolemy–Thompson group is of type F_∞*, Lemma 3.9 as corrected in
the erratum, verbatim): "Let Y be a compact m-dimensional combinatorial manifold. Let X be a
simplicial complex and assume that the link of every k-simplex in X is (m−k−2)-connected. Let
ψ : Y → X be a simplicial map whose restriction to ∂Y is simplexwise injective. Then after
possibly subdividing the simplicial structure of Y, ψ is homotopic relative ∂Y to a simplexwise
injective map."

Induct on the free count N. The base `N ≤ 10` is the w8 base cases. For `N ≥ 11`:
1. **Morse step.** By induction and (4.1), `(X_n(F), X^0)` is `η(N)`-connected,
   `X^0 = X_n(F ∪ {v, w})`. So it suffices that `π_m(X^0) → π_m(X_n(F))` is zero for `m ≤ η(N)`.
2. **Simplexwise injective (Lemma 3.1).** A k-simplex link in `X^0` is a family member of free
   count `M = N − 2k − 4`. Since `η(M) ≥ η(N) − k − 2`, the induction and the base give the
   hypothesis of Lemma 3.9. So `ψ : S^m → X^0` may be taken simplexwise injective.
3. **Push.** Apply (CX1) of `loop-braid-push-complexity-statement` to `K = ψ(S^m)`. This gives u,
   and a push `u'` with `ψ(lk x) ⊆ p L_e ⊆ lk(u) ∩ lk(u')` for every x over u
   (`loop-braid-pair-twist-push-mutual-link`).
   - `p L_e` has free count ≥ `N − 3`, so it is `(m − 1)`-connected by induction. Hence
     `{u, u'} * p L_e` is m-connected.
   - Redefining `ψ(x) := u'` is a homotopy in `X_n(F)`. The new map is still simplexwise injective
     and lands in `X^0`.
   - `Σ_x c(ψ(x))` drops.
4. **Termination.** When all complexities are 0, (CX0) puts ψ in `lk(b_0)`, and ψ is coned off in
   `St(b_0)`.
5. **Conclusion.** `π_j(X_n(F)) = 0` for `j ≤ η(N)`. Taking `F = ∅` gives
   `conn L_n(LB_*) ≥ ⌊(n−5)/3⌋ → ∞`.
