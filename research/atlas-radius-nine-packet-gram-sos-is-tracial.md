---
rg: 2
id: atlas-radius-nine-packet-gram-sos-is-tracial
kind: claim
title: The fixed A4 packet Gram and conditional-expectation SOS calculus is tracially blind
distinct_from:
  tracial-npa-cannot-separate-canonical-trace: that treats the standard truncated scalar moment hierarchy; this also covers finite-packet Reynolds expectations, operator-valued Gram matrices, and fixed Schur-complement manipulations.
  global-tracial-positivity-cannot-separate-group-trace: that is the semantic firewall for arbitrary universal tracial proofs; this identifies the concrete proposed radius-nine packet calculus as lying behind that firewall.
  radius-nine-pi-exterior-all-size-fence: that excludes bounded polynomial identities and fixed exterior powers; this excludes fixed positive-Gram and conditional-expectation inequalities, leaving neither of the two obvious finite-dimensional proof mechanisms.
---

Fix the finite A4 atlas packet groups and their word realizations.  Consider
the following certificate operations, with a fixed finite number of rows and
columns independent of the ambient matrix dimension:

1. evaluate fixed word `*`-polynomials and form fixed matrix amplifications;
2. apply a packet Reynolds operator

   ```text
   E_H(x)=|H|^(-1) sum_(h in H) rho(h)x rho(h)^*;       (PGS1)
   ```

3. form scalar or operator-valued Gram matrices

   ```text
   [E_H(a_i^*a_j)]_(i,j);                              (PGS2)
   ```

4. take positive linear combinations, principal compressions, traces, and
   Schur complements whose positive pivot is fixed or is regularized by
   `epsilon I`, `epsilon>0`; and
5. add sums of Hermitian squares and nonnegative multiples of squared atlas
   relator residuals.

Every inequality produced by this calculus is valid not only in matrices but
in every finite tracial von Neumann algebra carrying the same exact packet
representation.  In particular it is valid after substituting the left
regular representation of the atlas group.  Hence no such certificate can
prove a radius-nine polynomial `P` with

```text
P(U)+C D(U)>=0                  for every matrix tuple U,
tau_Gamma(P)<0.                                      (PGS3)
```

The obstruction persists if packet symmetry reduces `(PGS2)` to finitely many
isotypic scalar blocks or if a conditional-expectation contraction gives an
explicit dimension-free constant: those reductions use only finite matrix
algebra over the same tracial von Neumann algebra.

Therefore the residual route under `atlas-radius-nine-trace-separator` cannot
be closed by a fixed SOS assembled from packet symmetrization, positive Gram
forms, or ordinary Schur complements.  A successful universal all-size
matrix inequality must contain an operation which fails in a diffuse finite
tracial algebra--for example finite-rank/multiplicity integrality or a matrix
coordinate choice--and must then eliminate its amplification remainder at
positive normalized density.

This does not refute the radius-nine separator.  It fences the entire natural
packet-Gram SOS proof class and isolates the genuinely matricial ingredient
which any remaining certificate must display explicitly.
