---
rg: 2
id: atlas-one-cut-finite-multiplicity-extraction
kind: claim
title: Atlas microstates expose an asymmetrically leaking cut in the finite multiplicity algebra
artifacts:
  - notes/ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md
distinct_from:
  atlas-two-s3-covariance-collapse: that seeks direct covariance collapse of two fixed S3 directions; this target instead extracts a one-cut finite-multiplicity obstruction from the same canonical regular-A8 chart model.
---

For the canonical regular-`A_8` atlas model

```text
C^(20160 k) ~= l2(A_8) tensor C^k,
```

there are constants `C>0`, `c>0`, `c0>0` and a fixed construction, independent
of `k`, with the following property.  From every relative chart unitary `U`
whose canonical atlas packet has normalized-Hilbert--Schmidt defect `delta`,
the construction produces, in a fixed matrix amplification of the finite
multiplicity algebra `M_k(C)`, a projection `P` and a unitary `W` satisfying

```text
||(1-P) W P||_2^2 <= C delta^c,
||P W (1-P)||_2^2 >= c0 - C delta^c.                  (ACE)
```

The intended construction is the finite-coefficient shadow of the one-sided
comb compressor: after a fixed root-character/Pauli disintegration, the
lower-left cut should inherit its algebraic zero pattern while the
upper-right cut retains positive regular-character mass.

This claim is deliberately about the **finite multiplicity algebra**, not
ambient spectral projections in the group von Neumann algebra.  An intrinsic
ambient construction would also apply to the exact infinite-multiplicity
Leavitt model and cannot have a finite-trace Hall/one-cut deficit.

## Attempts

- **Explicit four-leg reduction.**  The live coordinate identity is now
  isolated as `atlas-four-leg-coordinate-frame-extraction`.  If
  `E_1,...,E_4` are the selected coefficient legs, take
  `P=E_1+E_2+E_3` and let `W` be the coefficient comb unitary.  Then the two
  leakages are exactly the sums of the three lower-left and three upper-right
  block masses.  A lower zero-row estimate together with one upper block of
  canonical mass `1/64` proves `(ACE)` with `c0=1/64`.
- **Canonical Pauli frame.**  Refuted as the desired frame:
  `TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT` gives mass `1/64` to every one of
  its sixteen blocks.  In particular its would-be forbidden lower row has
  mass `3/64`, so it cannot satisfy the first inequality of `(ACE)`.
  The missing operation is a noncanonical finite-multiplicity frame selection
  which matches the algebraic comb zero row to one retained positive Pauli
  block.
- **Bare four-by-four comb support.** Insufficient by itself: the required
  coordinate projections are not given as ambient group words. They must be
  recovered from a fixed finite root-character or Pauli decomposition of the
  canonical regular chart.
- **Ambient subgroup Fourier cut.** Useful for organizing the disintegration,
  but cannot itself be the final `P`; exact ambient support inclusions obey
  trace monotonicity even in the Leavitt group von Neumann algebra.
- **Root-character multiplicity cut.** Highest-value route. Use the fixed
  Heisenberg `z=-1` sector to obtain `C^2 tensor K`, identify the finite
  coefficient space `K`, and extract only enough of the comb transition to
  certify the two inequalities in `(ACE)`. This avoids reconstructing the
  full Leavitt coefficient algebra or four approximate inverse operators.
- **Falsification gate.** Before a quantitative proof, search for an exact
  finite regular-margin model of the selected boundary-plus-interior packet.
  Such a model would refute `(ACE)` immediately.
