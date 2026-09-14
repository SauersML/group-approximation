---
rg: 2
id: positive-entropy-el-groups-avoid-low-complexity-hosts-proof
kind: route
title: LEF growth is monotone under injective homomorphisms, and the cylinder lower bound beats the Rauzy-walk upper bound
target: positive-entropy-el-groups-avoid-low-complexity-hosts
requires: [subshift-elementary-group-lef-growth-complexity-bounds]
artifacts:
  - research/artifacts/sk-free-7-non-embeddability-2026-09-13.md
---

L_X(r) is the LEF growth of G_X for the note's generators (Bradford): the least order of a finite group admitting a map from the r-ball that is injective and multiplicative on products staying in the ball.

**Step 1 (monotonicity under embeddings).** Let ι: G_X → G_Y be injective. Let C be the largest G_Y-word length of the image of a generator of G_X.
- ι maps B_X(r) into B_Y(Cr).
- Let φ: B_Y(Cr) → H be a local model. Then ψ = φ∘ι is injective on B_X(r).
- For x, y, xy ∈ B_X(r), the three images ι(x), ι(y), ι(xy) = ι(x)ι(y) lie in B_Y(Cr), so ψ(xy) = ψ(x)ψ(y).

So L_X(r) ≤ L_Y(Cr). This is Step 2 of `recursive-lef-growth-hosts-miss-some-fp-rf-group-proof`.

**Step 2 (the two bounds).** By `subshift-elementary-group-lef-growth-complexity-bounds`:
- `L_X(r) ≥ 60^{p_X(⌈√(r/500)⌉)}` for r ≥ 125;
- `log_2 L_Y(r) < 9·N_Y(4r+1)^2` with `N_Y(n) ≤ (p_Y(n)+1)·p_Y(n−1) ≤ 2 p_Y(n)^2`.

So `log_2 L_Y(r) < 36·p_Y(4r+1)^4`.

**Step 3 (combine).** For r ≥ 125:

`p_X(⌈√(r/500)⌉) · log_2 60 ≤ log_2 L_X(r) ≤ log_2 L_Y(Cr) < 36·p_Y(4Cr+1)^4`.

Take r = 500k², so ⌈√(r/500)⌉ = k. Since log_2 60 > 5.9 and 36/5.9 < 7,

`p_X(k) < 7·p_Y(2000C k^2 + 1)^4 ≤ 7·p_Y(2001C k^2)^4` for k ≥ 1.

This is the Theorem with constant 2001C.

**Corollaries.**
- **Entropy.** h(X) > 0 gives p_X(k) ≥ e^{(h/2)k} for large k, so log p_Y(2001Ck²) ≥ (h/8)k − O(1). With n = 2001Ck², log p_Y(n) ≥ c√n along these n. Complexity functions are nondecreasing, so this holds for all large n up to a constant factor, contradicting log p_Y(n) = o(√n).
- **Polynomial scales.** c k^α ≤ 7·C′^4·(2001C)^{4β}·k^{8β} for infinitely many k forces α ≤ 8β.
- **Strict inclusions.** Combine with the factor embedding of `lef-growth-of-subshift-el-groups-is-monotone-under-factors`.

**Model tests.**
- X = Y: the inequality p_X(k) ≤ 7 p_X(Ck²)^4 holds trivially.
- The full shift is excluded (not minimal), but its minimal positive-entropy subshifts exist (Grillenberger), so the entropy corollary is not vacuous.
- A Sturmian Y has p_Y(n) = n+1, so every minimal X with p_X(k) ≥ k^9 infinitely often gives G_X ⊄ G_Y.
