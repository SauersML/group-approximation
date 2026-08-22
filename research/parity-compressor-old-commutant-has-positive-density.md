---
rg: 2
id: parity-compressor-old-commutant-has-positive-density
kind: claim
title: Couple a Schur Reynolds carrier to positive density in the parity compressor's old commutant
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that gives positive density in a local finite-packet commutant difference; this must place that range inside the old compressor commutant rather than on an independent tensor factor.
  packet-kazhdan-commutant-placement-decouples: that is the exact tensor-product countermodel to bare commutation relations; this requires coefficient covariance which excludes it.
---

Modify the Toeplitz parity compressor by one fixed Schur--Clifford packet and
coefficient-covariance cell so that, on every marked microstate with
positive forbidden carrier mass, a spectral subspace `W` satisfies

```text
W <= low-commutator space of Lambda,
tr_ad(W) >= c q^2-C sqrt(E),                            (PCD1)
```

where `q` is the forbidden Hilbert mass.  The placement must visibly fail in
the tensor-decoupled representation of
`packet-kazhdan-commutant-placement-decouples`.

Then `parity-twist-copies-the-old-commutant-into-the-excess` sends `W` to an
almost orthogonal copy in the compressed low-commutator space, and
`property-t-hs-positive-density-commutant-no-growth` charges its density to
normalized-HS relator energy.  This would prove the parity compressor return
on every positive marked carrier.

There is now a shorter canonical-trace endpoint.  By
`canonical-marked-corner-kazhdan-density-vanishes`, the old low-commutator
space itself has vanishing adjoint density in every canonical marked
microstate.  Hence `(PCD1)` already contradicts hyperlinearity; the parity
copy and relative no-growth argument are optional downstream structure, not
part of the remaining hole.

## Attempts

- Declaring both packet subgroups to commute with the two Kazhdan copies is
  false: the packet may live on an independent tensor factor and retain its
  full Reynolds gap at zero covariance cost.
- The local Schur theorem already supplies the density `c q^2`; the missing
  statement is an ordinary-word coefficient covariance that embeds its
  canonical three-generator Reynolds core into the compressor commutant.
- A finite controlled-phase overgroup cannot impose that covariance on every
  selector sector.  The live implementation must use the one-sided Toeplitz
  coefficient action or a projective two-cell.
- Even genuine finite automorphism covariance is insufficient.
  `finite-normalizer-covariance-density-no-go`
  takes regular semidirect quotients: the packet keeps constant Hilbert mass
  and constant Reynolds density while the old low-commutator density is
  exactly `1/|Q_n|`.  Thus a normalizer packet acting on all named
  coefficients still decouples asymptotically.  The one-sided Toeplitz cell
  must use non-surjectivity in an essential way; its induced finite head
  action cannot be the missing estimate.
- `commutant-density-forces-bounded-type-mass` identifies the exact burden
  of `(PCD1)`: a lower bound `c_0q^2` on the old adjoint commutant forces
  linear-in-`q` Hilbert mass in old-`Lambda` irreducibles of degree
  `O(1/q)`.  Thus the missing cell is quantitatively a bounded-type compiler,
  not merely a way to make the local Reynolds projection invariant.  Any
  proposed Toeplitz covariance must exhibit this conversion explicitly.
