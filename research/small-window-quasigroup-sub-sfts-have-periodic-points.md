---
rg: 2
id: small-window-quasigroup-sub-sfts-have-periodic-points
kind: claim
title: Every nonempty sub-SFT of a quasigroup spacetime of order at most 4 with a small row window has a periodic point
distinct_from:
  free-minimal-triangle-permutive-sft-exists: that asks for a free minimal sub-SFT at any window and alphabet; this decides the smallest windows for orders 2, 3 and 4, all negatively.
  permutive-triangle-sfts-are-quantum-rigid: that shows a periodic row forces a periodic point; this uses it as the certificate inside an exhaustive search.
artifacts:
  - experiments/triangle-permutive-sft-search-2026-09-17/README.md
  - experiments/triangle-permutive-sft-search-2026-09-17/search.py
  - experiments/triangle-permutive-sft-search-2026-09-17/run3.log
---

**ESTABLISHED (computer-assisted, unreviewed).** Let `(Q, ⋆)` be a quasigroup of order `k`, and let
`X_⋆ = {x ∈ Q^(Z^2) : x(z+e_2) = x(z) ⋆ x(z+e_1)}`. Let `Δ_L = {(i, t) : i, t >= 0, i + t <= L - 1}`. Let `Ω ⊆ X_⋆`
be a sub-SFT defined by forbidden patterns whose supports lie in translates of `Δ_L`. If

- `k = 2` (Ledrappier's shift) and `L <= 6`, or
- `k = 3` and `L <= 3`, or
- `k = 4` and `L <= 2`,

then `Ω` is empty or has a doubly periodic point. In particular, no free sub-SFT of Ledrappier's shift is defined
by forbidden patterns on `w × h` boxes with `w + h <= 7`.

**What this rules out.** Candidate examples for `free-minimal-triangle-permutive-sft-exists` in these small cases.
A free minimal example must use a larger window or an alphabet of order at least 5. Each extra unit of window
multiplies the number of window words by `k`.

**Method.**

- **Normal form.** Such an `Ω` equals `Ω(A)`, the set of points whose length-`L` row words lie in `A ⊆ Q^L`.
- **Periodic points.** `Ω(A)` has a periodic point iff `A` contains the window set of an `F`-cycle of spatially
  periodic rows.
- **Emptiness.** `Ω(A)` is empty iff some level shift `Z_n(A)` is empty. These shifts are presented by trimmed
  automata.
- **Search.** A complete branch and bound over essential window sets, with sound certification of long-period
  cycles, ends with zero surviving candidates in every case above. That is one quasigroup per isomorphism class:
  1, 5 and 35 classes.

The proof of soundness and completeness is in `small-window-quasigroup-sub-sfts-have-periodic-points-proof`.
