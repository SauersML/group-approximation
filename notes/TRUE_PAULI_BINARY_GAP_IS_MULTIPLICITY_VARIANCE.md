# The Pauli binary gap contains a fixed multiplicity-variance floor

Date: 2026-08-14

## 1. Outcome

The binary-algebra endpoint admits an exact orthogonal decomposition which
locates the hard part of the hyperlinear problem.  Keep the actual Pauli
packet

```text
E=PQ,        tau(E)=1/8,
F=U*QU,      tau(F)=1/4,
tau(EF)=1/32.                                      (PMV1)
```

Let

```text
S=2E-1,
Phi_E(X)=EXE+(1-E)X(1-E)=(X+SXS)/2.               (PMV2)
```

Thus `Phi_E` removes the off-diagonal Pauli blocks.  The conditional
expectation from the block-diagonal algebra to `W*(E)` then replaces each
diagonal block by its normalized scalar trace.

These are nested Hilbert--Schmidt orthogonal projections, so for every `X`,

```text
||X-E_(W*(E))(X)||_2^2
 =||X-Phi_E(X)||_2^2
  +||Phi_E(X)-E_(W*(E))(X)||_2^2.                  (PMV3)
```

The first summand is exactly the Pauli-parity defect:

```text
||X-Phi_E(X)||_2^2=(1/4)||[S,X]||_2^2.             (PMV4)
```

The second is the sum of the centered variances in the `E` and `1-E`
multiplicity blocks.

## 2. Exact split for the transported carrier

Put

```text
y=tau(EFEF)=||EFE||_2^2>=0.                         (PMV5)
```

For projections `E,F`, direct block expansion gives

```text
||F-Phi_E(F)||_2^2=2(tau(EF)-tau(EFEF)).            (PMV6)
```

Using `(PMV1)` and `(PMV5)`, the parity part is therefore

```text
parity(F)=1/16-2y.                                  (PMV7)
```

The full binary residual is `3/16` by
`TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md`.  Consequently the remaining
diagonal-block variance is

```text
multiplicity(F)=3/16-parity(F)=1/8+2y.              (PMV8)
```

Since `y>=0`, this proves the fixed floor

```text
boxed: multiplicity(F)>=1/8.                        (PMV9)
```

The scalar identities `(PMV7)--(PMV9)` are formalized source-first in
`GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean` as
`actualPacketResidual_split` and
`one_eighth_le_actualPacketMultiplicityResidual`.  No build or experiment
was run for this edit.

## 3. Consequence for the research program

This rules out a tempting simplification.  It is not enough to show that the
transported carrier asymptotically commutes with the parent sign `S`.
Commutation only kills `(PMV7)`.  Even if the parity defect vanished exactly,
the within-sheet coefficient variance would then equal the full `3/16`.

Nor can averaging over the fixed finite Pauli factor scalarize the remaining
blocks.  On a positive-density Pauli corner the exact normal form is

```text
M_2(C) tensor N,
E=e_11 tensor 1.
```

Conjugation by the Pauli sign removes the off-diagonal `M_2` entries, but its
fixed algebra is

```text
(e_11 tensor N) direct-sum (e_22 tensor N),          (PMV10)
```

not `W*(E)`.  The unresolved operation is precisely the replacement of the
two `N`-valued diagonal coefficients by scalars.  That is the
finite-multiplicity coefficient-recovery theorem; it cannot be supplied by
the fixed Pauli packet alone.

## 4. New smallest live gate

The binary-membership theorem can now be separated into two estimates:

1. **Parity rounding:**
   `||F-Phi_E(F)||_2 -> 0`.
2. **Multiplicity scalarization:**
   `||Phi_E(F)-E_(W*(E))(F)||_2 -> 0`.

Equation `(PMV9)` shows that the second estimate is indispensable and, for
the canonical packet, already contradicts a fixed `1/8` floor.  Therefore
the highest-yield next relation is not another finite Pauli commutator.  It
must be a cross-root multiplication relation which acts nontrivially on the
multiplicity algebra `N` and forces both diagonal coefficient blocks to have
vanishing centered variance.

This is a stricter and more informative endpoint than the phrase
“multiplication-module recovery”: the missing estimate is now exactly the
sum of two within-sheet conditional variances.
