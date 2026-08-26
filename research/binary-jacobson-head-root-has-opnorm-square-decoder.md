---
rg: 2
id: binary-jacobson-head-root-has-opnorm-square-decoder
kind: claim
title: Named Jacobson raw-root occurrences decode one square Toeplitz reservoir with a uniform modulus
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
  - research/artifacts/property-t-free-provenance-delta-2026-08-26.md
distinct_from:
  toeplitz-defect-needs-square-decoding: that establishes the terminal normalized-Hilbert--Schmidt trace payment after a square decoder and exhibits the exact rectangular escape; this asks the group presentation to extract the square decoder in operator norm from a surviving head root.
  opnorm-leavitt-coarse-fine-return-row: that seeks a common carrier for the full binary-Leavitt depth-one/depth-two packets; this is the unary one-branch Jacobson packet and only asks for its two one-sided inverse arrows on one selected corner.
  finite-weyl-root-moments-do-not-authenticate-toeplitz-square: that proves finite Weyl moments and pasted root triangles leave the rectangular Morita model exact; this requires a representation-dependent selector using a full-group incidence outside that interface.
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that gives marked finite partial models for the entire finitary head together with the literal Whitehead shift; this must use relations from the remaining Laurent-symbol elementary quotient.
  binary-jacobson-monomial-symbol-preimage-is-marked-mf: that enlarges the preceding cyclic subsystem to the preimage of every determinant-one monomial Laurent symbol and still retains the mark in an MF model; this must use the interaction with a raw nonmonomial Laurent root.
  binary-jacobson-elementary-symbols-have-zero-toeplitz-index: that proves the ordinary Laurent determinant/index boundary vanishes on every elementary symbol; this must recover a nonabelian same-square occurrence rather than an unbalanced Fredholm index.
  binary-jacobson-untyped-square-decoder-is-target-equivalent: that proves arbitrary coordinate-dependent Toeplitz data merely restate MF-invisibility; this requires a fixed occurrence package and a quantitative relator-to-decoder estimate.
  binary-jacobson-balanced-shift-transport-is-xor: that computes the first literal monomial/raw-root conjugation row and obtains only symmetric difference; this must add an authenticated occurrence which orients that row.
  binary-jacobson-three-cycle-is-controlled-swap-and-marked-mf: that closes three cyclic triangular rows to a head-controlled swap and proves that the three shifts, Weyl swaps, and one raw root in a common target column remain an amenable marked subsystem; this must leave that common-column semidirect product.
---

**OPEN.**  Let

```text
J=F_2<S,T | TS=1>,       Gamma_T=St_5(J),
Q=1-ST,                  w_T=x_13(Q).
```

Exhibit a fixed finite package of named words in a finite presentation of
`Gamma_T`, a deterministic finite-matrix operation using only evaluations of
those words (spectral cuts, intersections of commuting cuts, compression,
polar decomposition and matrix arithmetic), and a modulus
`omega(epsilon)->0` with the following property.

For every finite-dimensional unitary tuple `U` whose defects on the named
package are at most `epsilon` and whose rounded head cut is nonzero, that
specified operation produces:

* a nonzero projection `C_n` on the surviving spectral cut of the rounded
  head involution;
* a nonzero head projection `P_n<=C_n`; and
* contractions `X_n,Y_n in C_n M_(d_n)(C) C_n`

such that, uniformly in the dimension,

```text
max(||Y X-C||_op,||P-(C-X Y)||_op) <= omega(epsilon).  (JSD1)
```

Every output must retain its occurrence type: `C,P,X,Y` must be the stated
spectral/compressed/polar expressions in the fixed word evaluations.  It is
not enough to assert that some matrices satisfying `(JSD1)` exist after
seeing a surviving sequence; by
`binary-jacobson-untyped-square-decoder-is-target-equivalent` that assertion
is just the desired MF-invisibility theorem in disguise.

The selection may and must be representation-dependent, but its algorithm
and named occurrence package are fixed.  A fixed group-algebra projection or
fixed positive-root word cannot do this, because the regular representation
and the established rectangular Morita model satisfy the same finite
group-word interfaces.  The missing input is one authenticated mixed
incidence which erases the source/target object distinction on the selected
coordinate cut.

The finitary head and its literal Whitehead shift still do not suffice:
`binary-jacobson-finitary-whitehead-shift-is-marked-lef` periodizes every
finite inspected window while retaining the head root.  Thus the mixed
incidence required here must use a relation from the full
`EL_5(F_2[z,z^(-1)])` symbol quotient that is absent from that cyclic
subsystem.

The stronger monomial-symbol audit makes the first eligible relation exact.
`binary-jacobson-monomial-symbol-preimage-is-marked-mf` retains the whole
finitary kernel, all balanced Laurent translations and every Weyl
permutation in one regular-profile marked MF subgroup.  Adjoining the single
constant raw root `x_ij(1)` then generates the full elementary group (the
previous `S` and `T` seams are `K`-equivalent).  Therefore the decoder must
use the interaction of that nonmonomial elementary root with the monomial
preimage; no additional permutation, balanced-shift incidence, or
regular-character constraint can suffice.

Cycling the balanced shift through three source rows does not create the
missing orientation.  The exact product is a head-controlled swap, and the
subgroup generated by the three shifts, Weyl row swaps, one raw constant
root in a fixed target column, and the head root is amenable and marked MF
by `binary-jacobson-three-cycle-is-controlled-swap-and-marked-mf`.  Thus a
successful occurrence must couple different target columns or use a larger
piece of the monomial-symbol preimage than this cyclic actor.

The ordinary algebraic Toeplitz boundary does not supply that interaction.
`binary-jacobson-elementary-symbols-have-zero-toeplitz-index` shows that the
total index of every symbol in `EL_5(F_2[z,z^(-1)])` is zero.  The balanced
Whitehead lift cancels its two one-sided defects explicitly, while the
unbalanced Laurent unit of index one is unavailable in the elementary
quotient.  Thus the missing row is necessarily nonabelian occurrence data,
not a determinant or `K_1` pairing.

Once `(JSD1)` is proved, the sparse operator-norm clause of
`positive-toeplitz-head-is-square-defect-or-rectangular-escape` gives

```text
1 <= o(1)+o(1)/(1-o(1)),
```

a contradiction.  No positive-density bound, trace estimate, property
`(T)`, stability theorem, or branching argument remains after selection.
