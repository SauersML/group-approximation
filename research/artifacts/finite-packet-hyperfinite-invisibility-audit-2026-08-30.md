# Finite-packet hyperfinite-invisibility audit

## Result

The Clifford-compressor obstruction has been generalized to an arbitrary
finite semisimple representation packet and an arbitrary finite-order
central mark.  In each nontrivial central-character sector, the mark is
invisible whenever every fixed irreducible summand of each relevant
normalizer has a traceless implementer.  Moved summands contribute zero
automatically.
Compressor conjugacy then spreads those trace zeros across a nontrivial
abelian normal subgroup, and a nonamenable quotient acting essentially
freely on the subgroup's Haar dual supplies the contradiction.

## Checks

- Every root-of-unity spectral projection is central because the mark is
  central.  The proof is applied independently in each nontrivial sector.
- A representation of a finite central-character block may kill summands.  Its
  surviving central projections are permuted by each normalizer.
- A moved central summand gives an off-diagonal corner and hence zero trace.
- On a fixed surviving summand, unitality makes the matrix representation
  faithful; the corner splits as `M_d tensorbar W_0`, and the normalizer is
  the prescribed matrix implementer times a relative-commutant unitary.
- Vanishing on every nonidentity element of `N` identifies the spectral
  measure with Haar measure by uniqueness of Fourier coefficients.
- Haar-null fixed sets give proper outerness of the dual action, after which
  `hyperfinite-covariant-obstruction-lemma` supplies the contradiction.

## Scope boundary

The theorem does not construct a non-MF subgroup of `U(R)` and does not
resolve STW Problem X(2).  It excludes a larger family of proposed marked
witnesses.  For a fixed summand, the tracelessness hypothesis is essential:
a representation can concentrate on that summand when it is invariant and
its implementer has nonzero trace.  No condition is needed on summands that
the normalizer moves.

The previous signed-Clifford theorem is recovered from the negative spin
block of the relevant extraspecial two-group.  The new criterion also accepts
finite packets unrelated to Clifford algebras, blocks with several
irreducible summands, and odd-prime or general finite-order central marks, so
it is not a reformulation of the signed-cycle calculation.
