---
rg: 2
id: quadratic-overlay-has-uniform-linearized-synchronization-gap
kind: claim
title: The complete-pair overlay has a uniform linearized shared-face synchronization gap
distinct_from:
  repeated-ldpc-shared-face-marginal-synchronization: that is a global normalized-HS correction theorem; this proves only uniform transversality at an already exact shared representation
  repeated-ldpc-adjoint-face-hamiltonian-gap: that controls one matrix under conjugation by an exact face representation; this controls the full Jacobian of the occurrence presentation near an exact point
  normalized-hs-taylor-remainder-is-not-dimension-free: that obstructs a pure-HS Newton argument for arbitrary word maps; this identifies the positive linear estimate that survives before that obstruction
---

ESTABLISHED.  For the repeated occurrence presentation built from a positive-distance
binary code, equality expanders, and the explicit complete logical-pair
overlay of `quadratic-repetition-supports-complete-commutation-overlay`, with
the original parity layer repeated to constant density,
the derivative of the full occurrence-relator map has a dimension-independent
gap transverse to the exact representation variety.

More precisely, fix an exact finite-dimensional representation and normalize
the squared tangent norm by the number of occurrence variables and the
squared residual norm by the number of bounded-width occurrence relators.
If `D` is the derivative of the involution, equality, face-parity, and
within-face commutator relators, then

```text
  ||D xi||_2^2 >= kappa dist(xi,ker D)^2,                 (QLS1)
```

where `kappa>0` depends only on the code distance, the original row-width
and column-degree bounds, and the equality-expander gap.  It is independent
of code length, matrix dimension, character multiplicities, and the chosen
exact representation.

Here is the block calculation.  The exact quotient is the finite abelian
code-dual group, so decompose the Hilbert space into its joint character
spaces.  On a matrix block from character `chi` to character `psi`, put

```text
  z_i = chi_i + psi_i in F_2.                             (QLS2)
```

If `chi!=psi`, then `z` is a nonzero codeword and
`|supp(z)|>=delta L`.  After the harmless sign normalization of the tangent
coordinate `a_i`, the derivative of `[Q_i,Q_j]=1` is, up to a scalar of
absolute value two,

```text
  z_j a_i - z_i a_j.                                     (QLS3)
```

Consequently the complete logical pair energy on this block is the complete-
graph Poincare form

```text
 sum_(i,j) ||z_j a_i-z_i a_j||_2^2.                      (QLS4)
```

It vanishes exactly when `a_i=0` off `supp(z)` and all normalized `a_i` on
`supp(z)` are one common matrix.  That kernel is precisely infinitesimal
simultaneous conjugation on the `(chi,psi)` block.  Since
`|supp(z)|>=delta L`, the complete-graph Poincare inequality gives a gap
bounded below in the normalized variables by a constant depending only on
`delta`.  On a diagonal character block, the linearized involution equation
at the scalar reflections `+/-I` forces the tangent to vanish.  Orthogonality
of character blocks makes the same estimate valid for arbitrary
multiplicities.

The complete-pair overlay realizes every logical pair in one bounded-width
context, with uniformly bounded occurrence after quadratic repetition.
Replacing a context-occurrence tangent by the
mean tangent of its logical coordinate costs at most the equality energy:
the expander Poincare inequality bounds the mean squared occurrence variance,
and bounded occurrence bounds its contribution to the face derivatives.
Combining that estimate with `(QLS4)` proves `(QLS1)`.  The parity derivatives
are nonnegative extra terms and are not needed for the lower bound.

Thus the obvious infinitesimal soft modes are gone: neither growing
character multiplicity nor a high-rank direct sum can make the Friedrichs
angle between the local-face variety and the shared-coordinate variety tend
to zero.

This does **not** establish
`repeated-ldpc-shared-face-marginal-synchronization`.  A Newton or alternating-
projection argument also needs entry into one uniform nonlinear tube.  In an
operator-norm tube, the fixed-width word maps have

```text
  ||F(rho+xi)-F(rho)-D xi||_2 <= C ||xi||_op ||xi||_2,   (QLS5)
```

so `(QLS1)` gives a dimension-independent mixed-norm local correction
theorem.  Pure normalized-HS smallness supplies no such tube: concentrated
perturbations can have tiny `2`-norm and order-one operator norm, and the
quadratic remainder is then only linear in their `2`-norm.  Therefore a
linearized/Newton attack has now been reduced sharply to a **global basin
capture or truncation theorem**.  The adjoint face gap alone proves the
angle estimate but cannot supply that missing basin.
