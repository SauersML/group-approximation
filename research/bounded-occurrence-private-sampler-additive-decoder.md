---
rg: 2
id: bounded-occurrence-private-sampler-additive-decoder
kind: claim
title: Decode the selected private sampler labels by a linear-size bounded-occurrence code
distinct_from:
  bounded-template-average-blr-occurrence-decoder: that decodes the entire exponential simplex table; this asks only for the O(r squared) vector labels actually used by the private Weyl sampler.
  rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm: that rules out a uniformly conditioned linear rooted-sum formulation; this permits a nonlinear operator/PVM decoder but must explicitly evade that theorem.
---

OPEN.  For the recursive private sample labels

```text
(a_t,b_t)_(t<=C r^2)
```

construct, separately for the A and B lists, an `O(r^2)`-size,
bounded-degree, bounded-template, perfect-completeness occurrence test whose
selected coordinates occur `O(1)` times and whose near-perfect tracial
reflection strategies round on the same Hilbert space to

```text
U_t=X(a_t)       or       U_t=Z(b_t)
```

for one exact additive `F_2^r` action, with a dimension-independent average
normalized-HS modulus over `t`.

Auxiliary coordinates are allowed, but the total number of occurrences must
remain `O(r^2)` and each selected coordinate must have positive effective
test weight.  Scalar code soundness is insufficient: the decoder must kill
contextual noncommuting reflection representations.  Any linear extended
formulation must also address
`rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm` rather than assuming a
uniform checker constant.

The X- and Z-code incidence must additionally be compatible with the private
free-product sign placement: after the constant basins are attached, pure
same-basis paths may not create a sign-colliding short two-pair contour.
Mixed degree one alone does not exclude a contour closed through two distinct
anchor basins.

This is strictly smaller than global BLR decoding and is now the most
concrete positive same-basis target.  The private mixed placement, matrix
dimension witness, recursive label selection, and rooted-port interface are
all already established.

## Scalar and class-two feasibility audit

The independently random labels used in the present existence proof cannot
be checked directly by bounded-arity parities:
`independent-private-labels-have-growing-dual-distance` gives their dual code
distance `Omega(r/log r)`.  Auxiliary encoding or a redesigned sampler is
therefore mandatory.

On the other hand the full class-two obstruction fits inside the linear
budget.  `disjoint-private-pairs-expand-the-full-exterior-square` uses a
degree-one overlay on `O(r^2)` random selected labels and gives a uniform gap
on every nonzero alternating form.  Thus class two is not the terminal; after
it is killed, a nonnilpotent contextual quotient may still survive.

The concrete redesigned target is
`very-low-rate-ldpc-private-weyl-sampler`: start from a bounded-check length-
`Theta(r^2)`, dimension-`r` kernel, demand the private Weyl gap of its
coordinate functionals, add the exterior-square overlay, and prove
nonnilpotent operator rounding.

The scalar/dimension part of that redesign is now established by
`repeated-good-ldpc-coordinates-give-private-weyl-sampler`.  Quadratically
repeat an ordinary good length-`Theta(r)` LDPC code and match the repeated
coordinates privately.  Every coordinate is itself a positive-weight mixed
port, permutation concentration preserves the generator-column Weyl gap,
and a second degree-one matching kills the whole exterior square.  Thus the
only missing part of the present decoder is same-Hilbert exclusion or
stability of the remaining nonnilpotent contextual local-PVM quotient.

The exact part is now stronger:
`quadratic-repetition-supports-complete-commutation-overlay` uses the available
copies to test every base-coordinate pair at bounded occurrence, so every
zero-defect representation is already abelian and has one scalar-code PVM.
There is no exact nonnilpotent survivor.  Quantitative rounding remains open,
and `sparse-clifford-cycles-refute-average-commutator-rounding` proves that
average pair commutator energy alone is insufficient; the replicated LDPC
parity constraints must enter the estimate.

Theorem 3.11 of de la Salle cannot be used to supply this estimate directly.
As recorded in `de-la-salle-pauli-game-starts-after-the-same-pvm-gate`, the
theorem takes a single `2^r`-answer PVM on each side as primitive data.  Those
PVMs already are exact additive actions; the code columns provide only the
mixed spectral-gap sampler.  A bounded-occurrence group encoding of the PVM
is perfect-complete at zero defect, but its approximate synchronization is
exactly the present decoder claim.
