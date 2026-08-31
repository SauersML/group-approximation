# Audit: local-reconstruction subdivision firewall

Date: 2026-08-30

Claim: `stw81-local-reconstructive-subdivision-forces-af`.

## Quantitative audit

1. The two rows need not be unital or contractive in sum.  Positivity and
   `(LRS2)` give the order bounds `(NUR2)`, and division by the scalar upper
   bounds creates genuine subunital near-partitions.

2. The light row has fixed weight `gamma`, so its relative error is of order
   `epsilon/gamma`.  Taking `epsilon` to zero with `gamma` fixed makes both
   normalized defects vanish.

3. Projectionlessness is used after normalization and again in the scalar
   one-colour endpoint.  Cross-row orthogonality is unchanged by positive
   scalar rescaling.  The rotating overlap estimate gives a small colour in
   the first row for every fixed nonzero weight `1-gamma`.

4. No illegal amplification is used.  The surviving map is left unscaled
   and approximates `(1-gamma)id_D`.  The positive-scalar rigidity theorem
   handles this map directly, avoiding multiplication of either incoming or
   outgoing maps by a scalar larger than one.

## Subdivision audit

5. Repeating one incoming coordinate into finitely many direct-sum copies
   is c.p.c. regardless of the number of copies.  Regrouping same-labelled
   outgoing pieces is c.p.c. order zero because their ranges are pairwise
   orthogonal.  Thus subdivision depth contributes no norm factor.

6. The theorem permits the number of pieces to tend to infinity between
   approximation stages; each finite-dimensional factorization has only
   finitely many pieces.  The obstruction is therefore not merely a
   bounded-depth estimate.

7. Base-dependent cutdowns are included if they reconstruct each chart in
   the section algebra.  Evaluation at the selected transition point
   preserves all map properties and the reconstruction estimate.

## Exact remaining seam

The theorem does not cover a decomposition in which chartwise partial sums
have order-one errors which cancel only after the two charts are combined.
Nor does it cover an incoming map whose finite-dimensional coordinates are
intrinsically shared between charts, so that no chartwise c.p. maps
`S_i^r` exist.  These are two descriptions of the same remaining
incoming-coupled mechanism.

No lower bound on `dim_nuc(C([0,1]) tensor Z)` is asserted.

Outcome: **PASS**.
