---
rg: 2
id: two-qubit-pauli-automorphic-cell-dichotomy-proof
kind: route
title: Separate universal Pauli collapse from the virtually-free regular-flow branch
target: two-qubit-pauli-automorphic-cell-has-collapse-or-stationary-flow
requires:
  - two-qubit-pauli-frame-covers-common-d8-source
  - algebraic-selector-mixing-frame-collapses-forbidden-sector
  - central-character-regular-flow-defeats-finite-d8-return
  - residually-finite-models-refute-filtered-wandering-return
  - universal-block-return-violates-the-regular-firewall
---

Suppose first that the exact frame and mixing equations hold.  Equation
`(TPF6)` gives `4||F||_2^2` as the square defect of the literal mixed word;
equivalently the abstract frame calculation in `(ASM3)` gives `F=0` in every
representation satisfying the rows.  Therefore `F=0` in the universal
C-star algebra.  Since `F` is a nonzero projection of `C[K]`, the packet map
cannot be injective.  This also explicitly tests the induced-representation
model: its rejected `K`-type has nonzero `F`, so it cannot factor through the
collapsing quotient.

Now retain only the automorphic cells in the statement and assume that `K`
embeds.  Their presentation is the fundamental group of a finite graph of
finite groups.  The construction `(CCF2)--(CCF3)`, applied to the negative
character of the common center, gives matching endpoint restrictions on
every edge.  The central block of the regular representation is faithful,
so the nonzero projection `F` has positive trace in this representation.
Tree intertwiners identify the restrictions and the chord intertwiners are
arbitrary unitaries in their common multiplicity spaces.  This is precisely
the stationary-flow realization of the orthogonal-amalgam gauges; all
automorphic cells hold exactly and none removes `F`.

For the stronger window assertion, a finite graph of finite groups is
virtually free and hence residually finite.  Given a finite window, choose a
finite quotient separating its nonidentity words and all nonidentity
elements of `K`.  The quotient regular representation is faithful on `K`,
all relators hold exactly, and its restriction to `K` is a multiple of the
regular representation.  Consequently `tr(F)=tau_K(F)>0`, while every
separated nonidentity filter word has trace zero.  This is the exact
countermodel `(PAC3)` and contradicts `(PAC4)`.

Finally, a proposed proper-corner return cannot be promoted to a universal
block identity: cyclicity in the regular factor would force its positive
exit projection to vanish by `(UBR4)`.  Therefore the escape listed after
`(PAC4)` must use a finite-coordinate inference absent from the regular
factor, completing the claimed boundary.
