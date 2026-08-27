# The signed atlas certificate is tangent rigidity, not H-alignment

Date: 2026-08-13

## Outcome

The universal signed group-algebra certificate for the binary Leavitt atlas
does **not** prove that a finite relative chart implementer is close to the
commutant of

```text
H = diag(GL_3(F_2),1) < A8.                            (SAC1)
```

Its exact scope is first-order rigidity at the already aligned classical
fold.  Treating it as a nonlinear Hilbert--Schmidt estimate would silently
assume the main unresolved matrix-coordinate theorem.

## What the certificate proves

At the inner classical alignment, a two-chart word `q` with aligned value
one has a signed prefix derivative

```text
d_q in k[A8].                                         (SAC2)
```

For the certified-zero words and the four central survivor words, the
archived certificates prove that the marked phase derivative belongs to the
generated left ideal.  The calculation holds in characteristic zero and at
all exceptional primes, hence over every field.  It rules out every
square-zero deformation of this fixed fold on every finite-dimensional
module, including arbitrary multiplicities and indecomposable modules.

Equivalently: once a deformation has been placed in the tangent space at the
classical fold, vanishing of the selected first derivatives forces vanishing
of the marked first derivative.

## What it does not prove

Let `rho` be a regular multiple of the first chart and write the second chart
as

```text
g |-> U rho(g) U*.                                    (SAC3)
```

The certificate gives no estimate of

```text
delta_H(U) = max_(h in H) ||U rho(h)-rho(h)U||_2       (SAC4)
```

for an arbitrary unitary `U`.  In particular it supplies neither a path
from `U` to the aligned fold nor a dimension-independent inequality bounding
`delta_H(U)` by atlas relator defects.

There are two exact reasons this distinction is unavoidable.

1. The 234 boundary relations admit a finite affine countermodel with exact
   regular chart margins in which the two copies disagree on the standard
   generators of `H`.  Thus boundary-to-`H` alignment is false even before
   taking an ultralimit.
2. The full Leavitt group has its exact regular representation in `L(Q)`.
   All defining relations vanish there while the two copies of `H` remain
   distinct.  Hence no universal finite-von-Neumann-algebra inequality can
   force `(SAC4)` to vanish from the full relator packet.

The desired separation must use the finite chart multiplicity algebra in a
matrix coordinate, not merely the ambient tracial algebra.

## The exact remaining implication

The explicit Weyl bridge eliminates every algebraic step after `(SAC4)`.
If `epsilon_br` is the defect of its length-19 relation and `epsilon_int` is
the defect of the centrality relator from collision word 19243, then every
regular-margin finite matrix model satisfies

```text
sqrt(2) <= epsilon_int
           + 16 D (epsilon_br+9 delta_H(U)),
D <= 20159.                                            (SAC5)
```

Thus a hyperlinear atlas sequence would necessarily retain a fixed amount
of `H`-misalignment.  Proving nonhyperlinearity is now equivalent to ruling
out that finite-multiplicity misalignment by a matrix-specific argument.

The surviving mechanisms are correspondingly narrow:

* a finite gauge-index or invariant arrow-rank theorem for the regular-chart
  multiplicity quiver; or
* noncentral Pauli coefficient extraction which uses multiplication of
  Leavitt coefficients and lands in the finite multiplicity algebra.

Additive root windows, transfer of character marginals, and the isolated
finite Clifford packet do not suffice: each has exact finite completion
models already recorded in the atlas audit.

## Replay sources

The derivative certificate and its independent verification are in

```text
experiments/atlas_signed_group_algebra_irrep_screen.py
experiments/atlas_universal_signed_group_algebra.py
experiments/atlas-universal-signed-group-algebra-verification.json.
```

The finite boundary countermodel is documented in
`ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md`.  The Weyl bridge and `(SAC5)` are
documented in `TRUE_ATLAS_SINGLE_BRIDGE_SUBGROUP_REDUCTION.md`.
