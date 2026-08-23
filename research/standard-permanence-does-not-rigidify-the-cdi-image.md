---
rg: 2
id: standard-permanence-does-not-rigidify-the-cdi-image
kind: claim
title: Standard group permanence operations do not rigidify the CDI image character
distinct_from:
  ah-groups-fail-regular-fd-character-rigidity: that gives the intrinsic proper-ICC-quotient obstruction for the CDI source itself; this audits attempts to import rigidity from a different group by quotients, products, extensions, subgroups, or induction.
  cdi-character-cannot-be-promoted-by-regular-corners: that computes trace failure for central cuts, regular restrictions, marked corners and wreath carriers; this treats group-theoretic permanence around a separate rigid group.
  caprace-thom-v2-leaves-km-character-rigidity-open: that corrects one claimed Kac--Moody input; this shows why even a future positive Kac--Moody character theorem would still need control of the CDI kernel.
---

Let `pi:H->U(Q)` be the CDI representation with `Q` non-CE and let
`Lambda=H/ker(pi)`.  None of the following formal operations proves that
the factor character of `Lambda` is regular.

1. **A chosen quotient.**  A surjection `H->K` onto a character-rigid group
   is useful only if its kernel is contained in `ker(pi)`.  CDI universality
   does not prescribe `ker(pi)`, and the factor `Q` has no nontrivial von
   Neumann quotient on which to impose the missing relations.
2. **Products, free products and extensions.**  Any group with a proper
   infinite ICC quotient fails regular-or-CE factor-character rigidity:
   pull back that quotient's regular character.  Hence adjoining an infinite
   rigid quotient to the CDI source destroys the required rigidity on the
   enlarged group instead of transferring it to `Lambda`.  Tensoring the
   CDI representation with a regular representation of the rigid factor
   leaves the coefficient `chi(h)` visible on the complementary identity
   slice.
3. **Subgroups and induction.**  Restriction of a rigid group's regular
   representation remains regular and cannot recover the CDI character.
   Finite-index induction of a CDI factor representation would preserve a
   non-CE corner, but a finite extension of an acylindrically hyperbolic
   group is again acylindrically hyperbolic and therefore fails the needed
   rigidity.  Infinite-index induction has no normalized finite-factor trace
   on the natural coset amplification and supplies no extremal character to
   which rigidity applies.

The Kac--Moody proposal currently misses both inputs.  The simple Kazhdan
Caprace--Remy groups are not acylindrically hyperbolic: a non-elementary
acylindrically hyperbolic group has proper infinite ICC filling quotients,
whereas these groups are simple.  Moreover
`caprace-thom-v2-leaves-km-character-rigidity-open` records that the current
Caprace--Thom theorem proves IRS rigidity, not character rigidity.  Even if
the conjectural character theorem is later proved, CDI would yield the
bridge only after an additional theorem identifies the actual image
`H/ker(pi)` with such a Kac--Moody group.

Thus the surviving high-cascade target is exact and quotient-specific:
prove the hypothesis of
`cdi-character-rigid-image-quotient-is-an-exact-bridge` for the actual CDI
image, or construct factor-representation universality directly for a known
character-rigid group.  Standard permanence does neither.

