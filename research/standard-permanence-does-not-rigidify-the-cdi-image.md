---
rg: 2
id: standard-permanence-does-not-rigidify-the-cdi-image
kind: claim
title: Standard group permanence operations do not rigidify the CDI image character
distinct_from:
  ah-groups-fail-regular-fd-character-rigidity: that gives the intrinsic proper-ICC-quotient obstruction for the CDI source itself; this audits attempts to import rigidity from a different group by quotients, products, extensions, subgroups, or induction.
  cdi-character-cannot-be-promoted-by-regular-corners: that computes trace failure for central cuts, regular restrictions, marked corners and wreath carriers; this treats group-theoretic permanence around a separate rigid group.
  caprace-thom-v2-leaves-km-character-rigidity-open: that corrects one claimed Kac--Moody input; this shows why even a future positive Kac--Moody character theorem would still need control of the CDI kernel.
  faithful-irs-blocks-naive-ah-character-rigidity: that rules out naive faithful-character rigidity of the source without proving its fixed-point character is extremal; this audits the group operations needed to control the actual CDI image.
artifacts:
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

Let `pi:H->U(Q)` be the CDI representation with `Q` non-CE and let
`Lambda=H/ker(pi)`.  None of the following formal operations proves that
the factor character of `Lambda` is regular.

1. **A chosen quotient.**  A surjection `H->K` onto a character-rigid group
   is useful only if its kernel is contained in `ker(pi)`.  CDI universality
   does not prescribe `ker(pi)`, and the factor `Q` has no nontrivial von
   Neumann quotient on which to impose the missing relations.
2. **Products, free products and extensions.**  Any group with a proper
   infinite ICC quotient fails regular-or-finite-dimensional
   factor-character rigidity: pull back that quotient's regular character.
   This argument does **not** rule out regular-or-CE rigidity.  The pulled
   character has GNS factor `L(K)`, which is CE whenever the quotient `K`
   is hyperlinear; it is also nonfaithful and hence does not test the
   faithful-character condition for `Lambda`.  Thus retaining such a
   quotient obstructs the stronger classification, but supplies no transfer
   theorem for the weaker one.  Independently, tensoring the CDI
   representation with a regular representation of another group leaves
   the coefficient `chi(h)` visible on the complementary identity slice.
3. **Subgroups and induction.**  Restriction of a rigid group's regular
   representation remains regular and cannot recover the CDI character.
   Finite-index induction of a CDI factor representation would preserve a
   non-CE corner, but a finite extension of an acylindrically hyperbolic
   group is again acylindrically hyperbolic and therefore fails the stronger
   regular-or-finite-dimensional classification.  This does not itself
   exclude the weaker faithful regular-or-CE classification needed for the
   image bridge.  Infinite-index induction has no normalized finite-factor
   trace on the natural coset amplification and supplies no extremal
   character to which rigidity applies.

The Kac--Moody proposal currently misses both inputs.  The simple Kazhdan
Caprace--Remy groups are not acylindrically hyperbolic: a non-elementary
acylindrically hyperbolic group has proper infinite ICC filling quotients,
whereas these groups are simple.  The orthogonal Kac--Moody forms in
`orthogonal-kac-moody-forms-are-acylindrically-hyperbolic` do satisfy the CDI
source hypothesis, but no cited theorem gives them the required character
rigidity.  Moreover
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

Glasner--Hase add a compatible but carefully scoped obstruction.  Every
acylindrically hyperbolic source has a faithful nonregular fixed-point
character by `faithful-irs-blocks-naive-ah-character-rigidity`.  This rules
out rigidity of all faithful characters.  It does not by itself refute the
faithful **extremal** classification required for the particular CDI image,
because factoriality of that IRS character is an additional step.

## Scope correction, 2026-09-04

The earlier wording of item 2 incorrectly substituted "CE" for "finite
dimensional."  There is a direct counterexample to that stronger assertion.
Let `K` be the group of finitely supported permutations of the positive
integers, let `G=K x K`, and let `q` be projection onto the first factor.
The group `K` is infinite ICC and locally finite.  The quotient character
`chi_q(g,h)=delta_e(g)` is nonregular, nonfaithful, and extremal, with
infinite-dimensional hyperfinite GNS factor `L(K)`.  In fact every tracial
GNS algebra of the locally finite group `G` is hyperfinite, so all of its
factor characters are CE despite this proper infinite ICC quotient.

The proof in `cdi-rigidity-permanence-firewall-proof` gives the details.
This correction removes an invalid obstruction to the weaker classification;
it does not establish that classification for a CDI image.  The independent
calculation in `cdi-image-central-wreath-retains-the-regularity-gate` still
shows that the distinguished output character is regular exactly when the
input image character already is.  No nonhyperlinear group is constructed.
