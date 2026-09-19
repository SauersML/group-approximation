---
rg: 2
id: mixed-crt-iwahori-repair-reduction-proof
kind: route
title: Split the joint edge quotient by CRT and retain odd types as inert labels
target: mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
requires:
  - finite-group-multiplicity-mismatch-pays-hs-energy
---

Choose one dyadic exponent dominating `a,b` and one odd modulus divisible
by `m_+,m_-`.  The Iwahori subgroup is the inverse image of a subgroup
modulo `2`.  Hence CRT at the dominating modulus identifies its image with
the product of its dyadic image and its full odd image.  Taking the joint
image of the two edge maps (the second composed with the commensuration)
commutes with the two coordinate projections and proves `(MCR2)`.  The
commensurating diagonal is invertible at every odd modulus, so it merely
changes the odd projection by an automorphism; it does not couple the CRT
factors.

Every irreducible representation of either mixed vertex quotient is a
tensor product `alpha tensor gamma` of a dyadic and an odd irreducible.
The projection `O->O_+` (respectively `O->O_-`) is onto, so inflation of
`gamma` is irreducible.  Restriction to `D x O` is therefore

```text
(Res_D alpha) tensor omega.                              (MRP1)
```

Schur orthogonality makes different `omega` blocks disjoint.  This proves
the block formula `(MCR3)`, including the zero-column convention for an
odd type which does not factor through one vertex projection.

For the analytic estimate, let `rho,eta` be the two edge restrictions and
let

```text
beta(s)T=rho(s)T eta(s)^*
```

on normalized Hilbert--Schmidt matrices.  This representation factors
through a congruence quotient of the fixed finite-index subgroup `B` of
`SL_2(Z)`.  Selberg property `(tau)` applies to all congruence levels, not
only odd ones.  If `E` projects onto `Fix(beta)`, then

```text
||I-E(I)||_2 <= epsilon/kappa.                           (MRP2)
```

The polar support of `E(I)` is a common `Q`-subrepresentation of normalized
dimension at least `1-kappa^(-2)epsilon^2`.  For two equal-dimensional
finite-group representations, half of the dimension-weighted `L^1`
difference of their irreducible multiplicities is exactly the rank outside
their maximal common subrepresentation.  This gives `(MCR4)`.

Now assume the stabilized dyadic integer bound in `(MCR5)`.  Apply it to
the vectors in `(MCR3)` with weights `w_omega=dim(omega)`.  Realize the
corrected vectors by keeping common old irreducible blocks and changing
only the complementary blocks.  By `(MCR4)`, the changed normalized rank
on either vertex is at most `2H kappa^(-2)epsilon^2`; changing unitary
matrices on rank `r` costs at most `2 sqrt(r/d)` in normalized HS norm.
Thus, writing

```text
t=2 sqrt(2H) epsilon/kappa,                              (MRP3)
```

each corrected vertex is at generator distance at most `t`.  The corrected
edge restrictions now have identical multiplicities label by label.
Project the identity once more onto their exact mixed-edge intertwiner space
and take the polar unitary.  Their new edge defect is at most
`epsilon+2t`; applying `(MRP2)` and the standard isotypic completion of the
polar partial isometry gives `||V-I||_2<=4(epsilon+2t)/kappa`.
Conjugation costs at most twice this.  Hence the total movement is at most

```text
t+8(epsilon+2t)/kappa,
```

which is `(MCR6)`.

For necessity, a pure dyadic packet is the special case with trivial odd
quotient.  More generally, tensoring dyadic vertex columns with the odd
irreducibles that factor through the corresponding vertex projection
realizes every CRT-admissible labeled weighted system `(MCR3)` as a mixed
restriction problem.  Therefore a dimension-free mixed multiplicity repair
bound restricts to the stated label-stabilized dyadic bound.  The
equivalence is at the integer rounding gate; no claim is made here that the
presently known unlabeled dyadic constants are automatically label-stable,
nor that arbitrary formal labels not arising from an odd congruence quotient
are necessary test objects.
