---
rg: 2
id: fpbs-mal-finite-piece-bridges-pay-length-floor-proof
kind: route
title: Project a generating graphing of the bridge onto a transversal of its pieces, extract a treeing by nested Kruskal, and apply Gaboriau's treeing theorem and Theorem B
target: fpbs-mal-finite-piece-bridges-pay-length-floor
requires:
  - fpbs-mal-graphing-b-length-weighted-floor
  - gaboriau-treeable-free-action-realizes-min-cost
artifacts:
  - research/artifacts/fpbs-finite-piece-bridges-length-floor-2026-09-18.md
---

The complete proof is in the artifact, §§1–3.

1. **Projection** (Lemma 1.1). Let `Y` be a Borel transversal of `F`, with
   `x = κ(x) π(x)`, `κ(x) ∈ K`. A graphing `Ψ` with `F ∨ Ψ = E` splits by
   `(κ(x), label, κ(ψ x))` into pieces that project to partial maps
   `k'^{-1} g k` of `Y`. The projected graphing has the same cost and
   generates `E|_Y`. So `relC(E; F) ≥ C(E|_Y)`, and the labels only change
   inside `K g K`, so `b`-lengths are preserved.
2. **Treeing with short labels.** Applied to the generating graphing `G`,
   the projection gives a Borel graph `Q` on `Y` that generates `E|_Y`, with
   labels in `K lab(G)^{±1} K`.
   - (i) For hyperfinite `E`, write `E|_Y = ⋃ F_n` and build nested spanning
     forests `T_n ⊆ Q ∩ F_n` by the Kruskal rule for a Borel order. Then
     `T = ⋃ T_n` is a treeing of `E|_Y` inside `Q` (Lemma 2.1).
   - (ii) If `G` is a treeing with `F`-connected pieces, `Q` is already a
     treeing, since a `Q`-cycle lifts to a closed `G`-walk that uses some
     crossing edge exactly once (Lemma 2.2).
3. **Cost.** By `gaboriau-treeable-free-action-realizes-min-cost`, item 1,
   `C(T) = C(E|_Y) ≤ relC(E; F)`.
4. **Floor.** `F ∨ T ⊇ E`, so `R_K ∨ T = R_L`. By
   `fpbs-mal-graphing-b-length-weighted-floor` (Theorem B),
   `σ_b(X) ≤ Σ |γ|_{K,b} μ(D_γ) ≤ r C(T) ≤ r relC(E; F)`. Under weak
   containment in Bernoulli, the same claim gives `σ_b ≥ 1/80`.
