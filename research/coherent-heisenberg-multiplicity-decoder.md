---
rg: 2
id: coherent-heisenberg-multiplicity-decoder
kind: claim
title: Realize positive-density finite Heisenberg multiplicities on one Leavitt module
---

OPEN.  Let a normalized-Hilbert--Schmidt microstate sequence for the binary
Leavitt elementary group keep one fixed nonzero root a positive distance from
the identity.  Its finite additive and three-root Heisenberg windows determine
compatible multiplicity-density vectors by
`hs-finite-heisenberg-windows-have-compatible-density-measures`.

Construct coordinate projections of uniformly positive normalized trace and
four contractions on the corresponding corners satisfying the two inverse
relations and the binary sum relation of the Leavitt family, with
corner-normalized Hilbert--Schmidt defect tending to zero.

The finite windows already encode addition and multiplication.  The missing
assertion is that their compatible density data have one common
positive-density carrier on which all four coefficient operators coexist.

## Attempts

- **Take the inverse limit of the density vectors.**  This gives a measure on
  the inverse-limit type space, but not coordinate projections carrying four
  compatible matrices.  Positive root mass can drift through finer types so
  that every proposed nested coordinate carrier has vanishing trace.
- **Diagonalize the finite-group exactifications.**  Exactifications for
  different windows can require different small corrections and conjugating
  isometries.  Their scalar branching vectors agree while their matrix
  corners need not be nested or retain a positive common intersection.
- **Use the active root spectral projection.**  Its trace is positive when
  the root survives, but coefficient roots generally move it.  Compression
  back to that projection produces boundary errors not controlled by the
  finite-window multiplicities.
- **Use conditional expectations onto the finite-window algebras.**  The
  resulting martingale produces a limiting tracial sector, but the terminal
  Leavitt trace-floor theorem needs four contractions on actual matrix
  corners with uniformly positive relative dimension.

The remaining theorem is a positive-density gluing result, not another trace
inequality: compatible finite Heisenberg branching data must yield nested
coordinate carriers and coherent Leavitt operators.
