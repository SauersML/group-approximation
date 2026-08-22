---
rg: 2
id: higman-bs-product-holonomy-proof
kind: route
title: Gauge exact periodic packets and optimally match their Haar spectra
target: three-higman-bs-seams-vanish-fourth-is-product-holonomy
requires:
  - periodic-bs-clock-defeats-spectral-first-hit-checksum
---

Spectral invariance under squaring proves the packet classification exactly
as in the recorded `BS(1,4)` classification: finite positive multiplicities
make squaring permute the support; periodicity makes the eigenvalues odd-order
roots; equal multiplicity around each orbit gives the cyclic shift and its
arbitrary wrap monodromy.

For gauged copies, conjugating the difference `Z_i-C_i` by `G_(i-1)^*`
gives `(PH2)`, while the four successive gauge increments telescope to
`(PH3)`.  The converse defines `G_0=I`, `G_1=H_1`,
`G_2=H_1H_2`, and `G_3=H_1H_2H_3`; `(PH3)` closes the last increment.

For the clocks, the empirical eigenvalue measures of both `P_q` and `D_q`
converge weakly to Haar on the compact circle.  Hence their quadratic
Wasserstein distance tends to zero.  The finite normal-matrix matching
formula realizes the optimal eigenvalue assignment by a unitary `H_q`,
giving `(PH5)`.  With `G_i=H_q^i`, `(PH2)` gives the first three seams.
For the last, insert `H_q^4P_qH_q^(-4)` and conjugate `(PH5)` by `H_q^3`,
which proves `(PH6)`.  Finally the trace computation for the permutation
clock gives `(PH7)`.

