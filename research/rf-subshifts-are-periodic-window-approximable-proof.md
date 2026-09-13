---
rg: 2
id: rf-subshifts-are-periodic-window-approximable-proof
kind: route
title: Windows control closeness in the shift metric, so finite invariant window-SFT sets and Kerr–Nowak models convert into each other
target: rf-subshifts-are-periodic-window-approximable
requires: []
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

Artifact part 1, §1 (Lemma 1) and §2 (Proposition S). Metric `d(x,x') = 2^(-max{j : x|_(B_j) = x'|_(B_j)})` for an
exhaustion `e ∈ B_1 ⊆ B_2 ⊆ …`; shift `(g·x)(h) = x(g^(-1)h)`.

- **Lemma 1.** A finite `Γ`-set `E` with a map `ζ : E -> X` that is `ε`-dense and `ε`-close on `F` already gives
  RF: perfectness lets `ζ` be perturbed to an injective map, and uniform continuity absorbs the error.
- **⇐.** Given `F, ε`, take `B = B_j` with `2^(-j) < ε`, `W = B ∪ F^(-1)B`, and `O`. Choose `ζ(c) ∈ X` with
  `ζ(c)|_W = c|_W`. For `s ∈ F`, `b ∈ B`, `s^(-1)b ∈ W` gives `(s·ζ(c))(b) = (s·c)(b) = ζ(s·c)(b)`.
  Coverage of `L_W(X)` gives density. Apply Lemma 1.
- **⇒.** Given `W ⊆ B_j`, take a model `(E, β)` for `F = W^(-1)` and `ε = 2^(-j)`. Put
  `c_z(λ) = (β(λ^(-1))z)(e)`, so `c_(β(g)z) = g·c_z` and `O = {c_z}` is finite and invariant. Closeness gives
  `c_z(w) = (w^(-1)·z)(e) = z(w)`, so `c_z|_W = z|_W`. The same at `β(g^(-1))z` gives `O ⊆ X_W`. Density covers
  `L_W(X)`.
