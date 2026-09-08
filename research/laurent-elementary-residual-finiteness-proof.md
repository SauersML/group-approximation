---
rg: 2
id: laurent-elementary-residual-finiteness-proof
kind: route
title: Specialize the variable at a monic irreducible avoiding one nonzero entry
target: laurent-elementary-groups-are-residually-finite
requires: []
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

Let `g != I` in `EL_n(C[z,z^(-1)])` and pick an entry of `g - I` that is a
nonzero Laurent polynomial.

**Binary case.**  Multiply that entry by a power of `z` to get a nonzero
polynomial `f in F_2[z]`.  Choose a monic irreducible `h in F_2[z]`
dividing neither `z` nor `f`.  Such an `h` exists: given any finite list
of monic irreducibles, an irreducible factor of one plus their product
lies outside the list, and the list of irreducibles dividing `zf` is
finite.  In the finite field `K = F_2[z]/(h)` the image of `z` is nonzero,
hence invertible, so the specialization is a ring map
`F_2[z,z^(-1)] -> K`; and the image of `f`, hence of the chosen entry, is
nonzero.  Entrywise specialization is a group homomorphism into `GL_n(K)`
separating `g` from the identity, and it restricts to the elementary
subgroup.

**Integral case.**  The chosen entry has a nonzero integer coefficient;
choose a prime `q` not dividing it.  Reducing coefficients mod `q` gives
a nonzero element of `F_q[z,z^(-1)]`, and the binary argument applies
verbatim over `F_q`, producing a finite field `F_q[z]/(h)` in which the
entry stays nonzero.

In both cases every nonidentity element survives in some finite quotient,
which is residual finiteness.  A residually finite countable group is MF,
by the permanence facts recorded with the full-defect theorem.
