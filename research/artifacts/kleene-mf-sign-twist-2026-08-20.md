# Reverse-Kleene non-MF sign-twist audit

Date: 2026-08-20

## Question

Can the computational/self-referential machinery currently being developed for
a nonhyperlinear group be used to produce a non-MF group by a proof genuinely
different from the existing Kazhdan--Clifford non-MF argument?

## Established endpoint

Yes at the **reduction** level.  If a finitely presented source group has a
nontrivial involutive word `w` with a fixed finite-dimensional normalized-HS
collapse bound strictly below `sqrt(2)`, then adjoining a fresh central sign
`z` and one stable letter with

```text
a w a^-1 = z w
```

produces a finitely presented non-MF group.  The proof is
`hs-collapse-sign-twist-non-mf-proof`.

The mechanism is not the manuscript's property-(T) commutant transport.  On a
hypothetical `z=-1` norm-corona corner, the new relation makes `w` conjugate
to `-w`, hence forces its normalized trace to zero.  The source collapse gives
`||w-I||_2<sqrt(2)`, equivalently strictly positive real trace.  Contradiction.
Britton's lemma keeps the fresh sign nontrivial.

Combining this with the already-established reverse-Kleene proof gives
`reverse-kleene-involutive-compiler-gives-non-mf`: any HALT-survival /
NONHALT-HS-collapse compiler with an involutive mark yields a computable
finitely presented non-MF group.

## Strictly weaker MF compiler target

For MF one does not actually need normalized-HS soundness.  The theorem
`reverse-kleene-operator-norm-collapse-gives-non-mf` isolates the weaker
requirement:

```text
NONHALT + sufficiently small operator-norm relator defect
  => marked operator-norm distance < 1.
```

The reverse fixed point then contradicts the local MF separation constant
`1` directly.  This target quantifies only over worst-direction microstates;
it does not ask that a tiny corrupted computational sector be amplified to
positive normalized-HS density.  Thus the hyperlinear metapixel/return theorem
is not logically required for a computational non-MF proof.

## Why this is not yet a second unconditional construction

The intended Fanizza instantiation still stops at
`fanizza-native-signal-groupification`.  Cairn has the reverse-Kleene logic,
the native signal, and the BCS soundness estimate, but not yet the ordinary
group-word compiler for the nonlinear BCS predicates.  Claiming an
unconditional group from the HS version would therefore assume the live
hyperlinear bridge.

I also checked whether the affine relative-Leavitt Steinberg packet closes the
operator-norm compiler automatically.  It does not.  The established theorem
`affine-leavitt-steinberg-mark-is-fd-invisible` kills the active root in every
**exact** finite-dimensional representation, but a norm-corona representation
is represented by growing approximate matrix models.  Extending the exact
root-kernel argument to those models requires a matrix-specific
root-to-coefficient decoder; the existing open node
`affine-leavitt-steinberg-hs-coefficient-decoder` is stronger than needed for
MF, but exact finite-dimensional invisibility alone is insufficient (the
cyclic/BS calibration already demonstrates that logical gap).

## New live target suggested by the audit

The most economical computational non-MF backend is therefore not the full
HS return theorem.  It is an **operator-norm authenticated computation
compiler**:

1. encode the self-referential computation by finite spectral/multiplicity
   packets;
2. arrange that strategically changing one discrete packet type requires an
   operator-norm jump bounded away from zero;
3. use the reverse Kleene fixed point to make the marked word certify its own
   nontriviality;
4. on NONHALT inputs force the marked operator-norm distance below the MF
   separation threshold.

Operator norm makes rank and finite spectral type genuinely discrete: two
projections at distance `<1` have the same rank.  This is the specific place
where the MF compiler may be substantially easier than the normalized-HS
compiler.  What is still missing is a finite presentation whose recursive
cell naming/transition structure preserves that discreteness without a
runtime-dependent van Kampen loss.
