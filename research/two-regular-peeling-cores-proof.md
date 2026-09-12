---
rg: 2
id: two-regular-peeling-cores-proof
kind: route
title: Project partners into B, dualize left inverses to all functions, and propagate along live lines
target: two-regular-peeling-cores-carry-no-left-inverse
requires:
  - triangular-crossed-product-elements-are-units-or-zero-divisors
  - odd-measure-space-has-no-honest-thompson-compression
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Section 6 of the artifact.

**Projection.** `F_3[G \ H]` is an `F_3[H]`-sub-bimodule of `F_3[G]`, and `eps_-` is central in `F_3[H]`.
So `P(zeta x) = P(zeta) x` for `x in B`.

**All functions.** Once `zeta in B`, the identity `rho_mu(zeta) rho_mu(x) = 1` holds on `F_3^V`. Under
the pairing of functions with finitely supported vectors, `rho_mu(x)` is the dual of `rho_mu(x*)`.

**Back-substitution.** Each removed point is cleared by its unique removed column, which touches only
earlier points. The corrections are locally finite, so infinitely supported vectors are handled the same
way.

**Two-regular cores.**
- *Regularity.* `∫_(Pt_r) mult = ∫_(Col_r) deg = 2 lambda(Col_r) = 2 lambda(Pt_r)`, and `mult <= 2`, so
  `mult = 2`.
- *Lines.* Every entry is nonzero, so forced propagation gives a nonzero infinite kernel vector.
- *Cycles.* Clopen length bounds and compactness give bounded cycles.
  - A singular cycle block gives a finite kernel vector.
  - If every block is invertible, the diagonal of earlier rounds plus the live blocks is a unit `D`.
    `D^-1 (x - D)` is nilpotent, so `x` is a unit, which is excluded.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 20 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the bimodule projection, with `eps_-` central;*
- *finite-radius identities holding on all functions;*
- *Haar balance forcing `mult = 2`, line propagation with locally finite back-substitution, and bounded cycles.*
