---
rg: 2
id: perfect-zpc-irs-quantum-gap-game
kind: claim
title: A finite tailored game has a perfect ZPC-IRS strategy but quantum value below one half
distinct_from:
  manzoor-irs-quantum-value-gap: that proves an unrestricted IRS-strategy gap with no perfect-completeness conclusion; this strengthens it to a perfect gap in the Z-aligned edge-commuting tailored class.
  phase-safe-toric-gap-game-exists: that asks for a phase-safe toric/LCS-style game whose perfect model directly compiles to a group; this proves perfect completeness already exists in the broader tailored ZPC-IRS class, leaving readable-control elimination as the remaining groupification step.
  hyperlinear-quotient-permanence-equivalence: that is the abstract universal-hyperlinearity boundary; this is a concrete finite game separation forced by TailoredMIP undecidability.
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

There exists a finite tailored non-local game `G` such that

```text
omega_ZIRS(G)=1,
omega*(G)<1/2,
```

where `omega_ZIRS` is the value over Z-aligned, edge-commuting IRS strategies.
Moreover the value one is attained by an actual ZPC-IRS strategy.

This existential attainment supplies no affine-Haar selection theorem.
`zpc-does-not-force-affine-haar-membership-law` proves that the defining ZPC
axioms and perfect acceptance are compatible with a membership Fourier moment
of modulus `1/3`, while
`affine-haar-membership-does-not-promote-irs-trace` proves that even a strategy
whose membership law passes every affine-Haar moment test would not thereby
place its IRS GNS algebra in the associated algebraic crossed product.  Thus
the affine-envelope route needs both special joint-cylinder data and a
separate trace-preserving retention of the non-CE relation normalizers.

The proof combines TailoredMIP*=RE with the computable decreasing hierarchy
`zpc-irs-value-computable-upper-hierarchy`.  If every non-halting TailoredMIP
instance had ZPC-IRS value strictly below one, that decreasing hierarchy and
the standard computable increasing quantum-value hierarchy would decide the
halting problem by waiting for either `alpha_t^Z<1` or `beta_t>=1/2`.
