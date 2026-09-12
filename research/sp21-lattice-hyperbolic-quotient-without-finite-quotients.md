---
rg: 2
id: sp21-lattice-hyperbolic-quotient-without-finite-quotients
kind: claim
title: A torsion-free cocompact Sp(2,1) lattice has an infinite hyperbolic quotient without finite quotients
distinct_from:
  kazhdan-hyperbolic-group-without-finite-quotients: that asks for some hyperbolic Kazhdan group without finite quotients; this pins the group to a quotient of one fixed arithmetic lattice, and the two are equivalent through the fixed-host reduction
  torsion-free-hyperbolic-kazhdan-partner-exists: that is the established existence of the lattice, which is linear and residually finite; this asks for a quotient of it without any finite quotient
---

Let `Γ` be a torsion-free cocompact lattice in `Sp(2,1)`.  Exhibit a normal
subgroup `M` of `Γ` such that `Γ/M` is infinite, word-hyperbolic, and has no
nontrivial finite quotient.

Such a quotient is Kazhdan, non-MF, and not residually finite.  By
`hyperbolic-rf-question-reduces-to-one-fixed-host` this claim is equivalent to
`non-residually-finite-hyperbolic-group`, and quotients injective on any
prescribed ball of `Γ` then exist.

## Attempts

- **Fixed-host reduction.**  The route
  `sp21-lattice-quotientless-quotient-via-host` derives it from any
  counterexample.  So it is exactly as hard as the root.
- **Profinite density.**  `Γ/M` has no finite quotient iff `MN = Γ` for every
  finite-index normal `N` of `Γ`, i.e. `M` is dense in the profinite completion
  of `Γ`.  Any `M` contained in a proper finite-index subgroup of `Γ` fails.  So
  a witness `M` must surject onto every finite quotient of `Γ` (in particular
  every congruence quotient) while staying small enough to keep `Γ/M` infinite
  and hyperbolic.  No such `M` is known.
- **Simple-quotient bound (2026-09-12).** Density is automatic except against
  finitely many simple images, provided the lattice has only finitely many
  alternating and large-rank simple quotients.
  - Route `quotientless-hyperbolic-via-sp21-simple-quotient-bound` builds `M`
    from two Olshanskii quotients that are surjective on deep finite-index
    subgroups.
  - The hypothesis is `sp21-lattice-few-alternating-and-large-rank-quotients`.
    It is implied by the congruence subgroup property and weaker in form.
  - So the open part of this claim is exactly the alternating and
    unbounded-rank images of the lattice.
