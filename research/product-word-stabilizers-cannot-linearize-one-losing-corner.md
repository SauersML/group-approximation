---
rg: 2
id: product-word-stabilizers-cannot-linearize-one-losing-corner
kind: claim
title: Product-word stabilizers cannot functorially cut out three corners of a Boolean rectangle
distinct_from:
  spherical-root-type-selection-is-phase-unsafe: that is a normal-closure/type-selection obstruction for finite spherical packets; this is the direct-product locality obstruction even before normal closure
  finite-morita-toricization-cannot-encode-nonaffine-support: that uses centers and induction to force affine support; this is an elementary fixed-space theorem for arbitrary local Hilbert-space ancillas
---

ESTABLISHED.  Let

```text
H_A=H_A^0 directSum H_A^1,
H_B=H_B^0 directSum H_B^1
```

with all four summands nonzero.  Let `U_j=A_j tensor B_j` be any finite
family of product unitaries and let `lambda_j` be scalar phases.  Suppose every
`U_j` acts as `lambda_j I` on each of the three allowed Boolean rectangles

```text
H_A^0 tensor H_B^0,
H_A^0 tensor H_B^1,
H_A^1 tensor H_B^0.                                  (PWS1)
```

Then every `U_j` also acts as `lambda_j I` on the forbidden rectangle

```text
H_A^1 tensor H_B^1.                                  (PWS2)
```

Consequently no finite family of scalar product-word stabilizers has common
fixed space equal to the kernel of one nontrivial joint losing projection
`P_A^1 P_B^1` while preserving every allowed vector.

## Proof

Fix `j`.  From scalar action on `H_A^0 tensor H_B^0`, the restrictions of
`A_j` and `B_j` to the two factors are scalar, say `alpha_0 I` and
`beta_0 I`, with `alpha_0 beta_0=lambda_j`.  This elementary tensor fact
follows by fixing a nonzero vector in one factor and comparing simple tensors.

Scalar action on `H_A^0 tensor H_B^1` then forces
`B_j|H_B^1=beta_0 I`.  Scalar action on
`H_A^1 tensor H_B^0` forces `A_j|H_A^1=alpha_0 I`.
Their tensor product on the fourth rectangle is therefore
`alpha_0 beta_0 I=lambda_j I`, proving `(PWS2)`.

The argument is per stabilizer, so adding finitely or infinitely many product
words does not help.

## Scope

Every word in a direct-product player group splits as an Alice word times a
Bob word, so the theorem applies after arbitrary **local** finite ancilla
extensions.  It rules out a representation-functorial exact reset which
turns the nonlinear reflection

```text
1-2 P_A^1 P_B^1
```

into scalar product-word stabilizers while retaining the whole allowed
subspace.

It does not rule out a compiler tailored to one entangled/tracial state.
Product stabilizers can characterize a Bell state, so a state-dependent
compiler may deliberately sacrifice most allowed vectors.  But then its
soundness must concern the entire resulting clause face and exclude every
finite-dimensional state in that face.  That is exactly
`central-word-state-face-compiler`, not a local ancilla identity.

## Attempts

The attempted construction block-encodes the joint losing reflection using a
finite transitive control register and local controlled words.  If the block
encoding preserves the reflection on every allowed source vector, `(PWS1)`
applies and the forbidden corner is also fixed.  Restricting to one selected
entangled root avoids the theorem, but then the spherical root faces the
normal-closure dichotomy in
`spherical-root-type-selection-is-phase-unsafe`.

