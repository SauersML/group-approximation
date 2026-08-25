---
rg: 2
id: atomwise-schur-pauli-cycle-return
kind: claim
title: Return the named forbidden-atom Schur flags through one matrix-only cycle
distinct_from:
  finite-phase-tags-authenticate-forbidden-cuts: that is stated for arbitrary forbidden-weighted analytic selectors; this is the reduced gate after atomwise coordinate coding and literal Schur--Pauli flag construction.
  relative-rank-one-fanizza-groupification: that propagates a Turing BCS recurrence through a one-sided valuation clock; this asks only for the fixed shared non-CE BCS and one finite global cycle over its forbidden atoms and packet types.
  common-partial-isometry-swap-game-compiler: that asks for a common Gram-source compiler before the selector cuts are named; here every source and target flag is already a finite polynomial in fixed packet words.
  one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum: that refutes a single uncompressed transport word with an arbitrary last-edge gauge; this permits the compressed K2,m rectangles and requires the remaining Pauli-flag row to be charged by the shared BCS payload.
---

**OPEN ATOMWISE RETURN GATE.**  Use the fixed Schur--Clifford packet for each
predicate in the shared non-CE BCS.  Index the finite menu by forbidden
assignment atoms and marked packet types.  On every menu element use the
literal projections `e_omega,f_omega` from
`schur-pauli-words-name-atomwise-half-quarter-flags`.

Construct a finite ordinary group-word actuator, a permutation `sigma` of
the menu, decoded unitaries `U_omega`, and a dimension-independent constant
`K` such that every sufficiently accurate finite-dimensional canonical
microstate satisfies

```text
sum_omega ||U_omega e_omega U_omega^*
                    -f_(sigma(omega))||_2^2
 <=K E_actuator+o(1).                                  (ASR1)
```

The actuator must extend the perfect commuting non-CE model with its common
central mark nontrivial.  The coordinate covariance rows may be used to
match assignment atoms, the phase-code rows to match packet types, and the
compressed `K_(2,m)` rectangles to remove the last multiplicity gauge.

All nonlinear selector syntax has already disappeared from `(ASR1)`:
`e_omega` and `f_omega` are intersections of spectral halves of named
involutive words.  The remaining content is a finite-coordinate return of
one relative Pauli half to one relative-plus-baseline Pauli quarter.  It
must be matrix-only.  Imposing their equality as a universal corner identity
would contradict the regular trace, while a finite graph of packet HNN edges
admits the known exact multiplicity-gauge escape.

Thus a proof must identify the compressed row with shared-payload energy, or
use another finite-matrix invariant that fixes the common multiplicity
reservoir.  Finite-group exactification, phase covariance, and the literal
Pauli formulas alone do not prove `(ASR1)`.

The target-capacity reformulation makes the available front end stronger.
By `dyadic-pauli-payload-flags-supply-strict-target-capacity`, finitely many
additional baseline Pauli pairs name, on the same atom, a source half `E` and
a target `F_n` with

```text
tau(F_n)=(2-2^(1-n))tau(E)
```

for arbitrary fixed `n`.  Combining this with
`rectangular-three-row-cell-forces-double-target-capacity` would require only
two diagonal inverse rows and one crossed-zero row through that pair; no exact
half-to-quarter conjugacy or full menu permutation is necessary.  The
regular-trace fence remains identical: those three rows must be decoded only
in finite canonical microstates, not imposed as literal packet identities.

## Attempts

- The relative and baseline Pauli words remove the additive-selector and
  arbitrary-subprojection objections.  They do not remove the last-edge
  multiplicity gauge; Bass--Serre amplification can still cancel a local
  factor-two branching discrepancy.
- A direct pair of conjugacy relators would identify the corresponding
  packet words in every representation and fail the regular-trace firewall.
  The comparison must occur only after the matrix-coordinate `K_(2,m)`
  compression or an equivalent reservoir lock.
- Twisting the commutator of the two Schur packet flips does create a genuine
  payload-conditioned multiplicity law, but
  `twisted-flip-square-shifts-multiplicity-cocycle` shows that it only moves a
  fixed parity divisor between allowed and forbidden sectors. Its defect is
  `O(1/m)` on multiplicity `m`, so it cannot pay `(ASR1)` without an
  independent positive-density or supercritical-rank amplifier.
- Fixed PI degree is a possible detector only after the transported target
  words are forced to generate the full transverse factor on positive
  trace.  That fullness is not a consequence of the named Pauli pair.
- Replacing the rectangular occurrences by Pauli/Clifford normalizers cannot
  exploit the new dyadic deficit.  By
  `two-affine-half-rows-pay-deleted-dyadic-atom`, the two diagonal Gram losses
  plus the crossed Gram have squared sum at least the mass of the deleted
  deepest flag atom.  Thus every affine flag routing pays the exact deficit
  it was meant to hide.  At least one live row must be a genuinely
  nonnormalizing coefficient occurrence coupled to the same payload atom.
- A finite typed opposite-root/Whitehead chart still does not suffice.
  `finite-bass-serre-dyadic-cell-has-exact-countermodel` passes any
  finite graph-of-finite-groups packet attachment to one exact finite regular
  quotient.  The named dyadic pair keeps its strict capacity deficit there,
  so the three compressed rows have a fixed positive floor although all
  defining relators are exact.  The surviving occurrence must therefore use
  a genuinely non-semisimple coefficient vertex, not merely the order-four
  Whitehead product or a finite cyclic/HNN interface.
- The full signed affine-Leavitt vertex is the first remaining candidate, but
  its use is already nonhyperlinearity-strength.
  `ordinary-leavitt-quotient-fences-whitehead-active-floor` shows that a
  dimension-uniform active occurrence profile would make the explicit
  ordinary Leavitt quotient nonhyperlinear.  Thus the unresolved actuator is
  a noncentral payload-to-coefficient coupling beyond the finite edge, not a
  missing local Whitehead multiplication identity.
