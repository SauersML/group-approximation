# Finite-packet hyperfinite-invisibility audit

## Result

The Clifford-compressor obstruction has been generalized to an arbitrary
finite representation packet.  A central involution is invisible in every
finite injective representation whenever its negative block in one finite
subgroup is a single full matrix algebra, the relevant normalizers have
traceless implementers in that block, compressor conjugacy spreads those
trace zeros across a nontrivial abelian normal subgroup, and a nonamenable
quotient acts essentially freely on the subgroup's Haar dual.

## Checks

- The negative spectral projection is central because the mark is central.
- A unital representation of the simple block `M_d` is injective.
- A finite von Neumann algebra containing a unital `M_d` splits as
  `M_d tensorbar W_0`, and every normal trace splits as the normalized matrix
  trace tensored with a normal trace on the corner.
- Normalizer implementers differ by a unitary in the relative commutant;
  this is the only factorization needed for trace zero.
- Vanishing on every nonidentity element of `N` identifies the spectral
  measure with Haar measure by uniqueness of Fourier coefficients.
- Haar-null fixed sets give proper outerness of the dual action, after which
  `hyperfinite-covariant-obstruction-lemma` supplies the contradiction.

## Scope boundary

The theorem does not construct a non-MF subgroup of `U(R)` and does not
resolve STW Problem X(2).  It excludes a larger family of proposed marked
witnesses.  Simplicity of the negative finite block is essential to the
statement as written: with several irreducible summands, a representation
can concentrate on a summand whose implementing trace is nonzero.

The previous signed-Clifford theorem is recovered from the unique spin block
of the relevant extraspecial two-group.  The new criterion also accepts
finite packets unrelated to Clifford algebras, so it is not a reformulation
of the signed-cycle calculation.
