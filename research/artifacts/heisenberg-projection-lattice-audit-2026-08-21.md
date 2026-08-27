# Heisenberg-pinned projection-lattice audit

Date: 2026-08-21.

The proposed escape starts with a countable dyadic projection lattice in a
separable non-Connes-embeddable factor, refines each finite commuting context
into equal atoms, and attaches a finite Heisenberg packet with one common
central involution `J`.  Cutting to `J=-1` does fix each local packet up to
multiplicity.  The question was whether literal common Pauli elements or
common subgroup data can also identify all coarse projections across charts.

The answer for that precise language is no, for a reason stricter than the
generic external-multiplicity gauge.  In the unique spin representation of
an extraspecial `2`-group:

- one Pauli spectral cut is always a balanced half;
- a common-character cut for an isotropic rank-`r` subgroup is a stabilizer
  code of normalized trace `2^(-r)`; and
- in a maximal commuting context, such a code is exactly the sum of atoms in
  one affine flat of the character space.

Fourier uniqueness of the Pauli basis further shows that equality of two such
cuts forces the same isotropic subgroup and the same character.  Thus common
subgroup data do not secretly identify a nonlinear union of atoms.  A
three-of-eight coarse projection is the smallest explicit witness.

This blocks a Dye reconstruction based solely on literally shared Pauli
elements/subgroups: those cuts do not even have a dense trace set, before one
asks for preservation of orthogonality or arbitrary cross-chart overlap.
The remaining possible escapes all require an additional operation not
present in the proposal: Boolean sums as named group-algebra projections, a
finite overgroup whose non-Pauli data selects the sum, or a transport gadget
that carries a non-scalar projection through the common corner.  Those return
to Cairn's signed-Hecke/projection-atlas compiler rather than bypassing it.

The exact theorem and proof are
`heisenberg-subgroup-cuts-are-affine-stabilizer-flats` and
`heisenberg-subgroup-cuts-affine-proof`.
