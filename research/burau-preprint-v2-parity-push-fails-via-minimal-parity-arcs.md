---
rg: 2
id: burau-preprint-v2-parity-push-fails-via-minimal-parity-arcs
kind: route
title: "Parity-clean arcs realize the geometric intersection number, so the equal-count obstruction applies to v2 verbatim"
target: burau-preprint-v2-parity-push-fails-for-a-brunnian-four-braid
requires:
  - parity-correcting-push-fails-for-a-brunnian-four-braid
artifacts:
  - research/artifacts/zp-burau-v2-audit-2026-09-19.md
  - experiments/burau-v2-audit-2026-09-17/section7_parity_calibration.py
---

Artifact §1 and §3, Proposition 3.1.

1. *The definitions agree.* v2's disk sequence, winding numbers, Lemma 3.1 (`W_i = k_{i+1} − k_i`)
   and parity condition, read verbatim from the v2 PDF, are those used by the prerequisite. The
   inclusion `f` is the standard one (Observation 2.1). Artifact §1 quotes them.
2. *Parity from the preprint's text.* `|P(∆_i)| = |W_i| = |k_{i+1} − k_i|`, so the parity condition
   says `ε_{i+1}(−1)^{k_{i+1}} = ε_i(−1)^{k_i}` for all `i`. Hence a parity-clean representative
   with `m` crossings has `|M(−1)| = m`.
3. *Parity-clean representatives are minimal.*
   - `M` depends only on the homology class, the fact used in v2's proof of Theorem 2.3.
   - Computing `M` on a minimal representative gives `|M(−1)| ≤ ι`.
   - With 2, `m ≤ ι ≤ m`, so `m = ι`.
4. *Conclusion.* Let `Φ = y Φ_0^k y^{-1}` and `Γ ∈ B_5`.
   - By `parity-correcting-push-fails-for-a-brunnian-four-braid`, parity-clean representatives
     of `(β_*^3) f(Φ)Γ` and `(β_*^3)Γ` cross `α` equally often. That claim holds for every
     `Γ ∈ B_5`.
   - By 3, those counts are the two `ι`. ∎

Calibration: the three Moody polynomials printed in v2's Section 7 satisfy
`parity ⟺ |M(−1)| = m` exactly as the authors label them (script log: `True`).
