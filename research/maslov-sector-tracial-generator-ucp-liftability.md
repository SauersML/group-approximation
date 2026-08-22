---
rg: 2
id: maslov-sector-tracial-generator-ucp-liftability
kind: claim
title: Maslov-sector homomorphisms into tracial matrix ultraproducts lift ucp on the canonical generators
distinct_from:
  sp4-mod3-twisted-fibres-have-llp: LLP lifts every ucp map to every quotient locally on every finite-dimensional operator system; this asks only for coordinate ucp representatives of homomorphisms from one Deligne twisted fibre into tracial matrix ultraproducts, on its canonical generator system.
  llp-implies-weak-ucp-stability: that is a general group-level consequence of LLP; this is the exact strictly weaker lifting assertion needed for the two nontrivial projective sectors.
---

Let `A_alpha = C^*(Sp_4(Z);alpha)` for a nontrivial mod-three Deligne
multiplier, and let `u_s` be its canonical unitaries for a fixed finite
generating set.  Given any star-homomorphism

```text
Theta : A_alpha -> prod_omega M_(d_n)
```

into a tracial matrix ultraproduct, prove that there are ucp maps
`phi_n:A_alpha -> M_(d_n)` such that

```text
Theta(u_s) = [(phi_n(u_s))_n]                              (TGL1)
```

for every canonical generator `s`.

This is much weaker than LLP: the codomain quotients, maps, and operator
system are all fixed to the tracial matrix/canonical-generator situation.
Nevertheless it closes the Maslov sector by
`brown-ucp-generator-lift-closes-maslov-gap`.

## Attempts

- Lift `Theta` first through the free full group C-star algebra, where chosen
  unitary representatives give exact coordinate star-homomorphisms.  The
  presentation relators vanish only in normalized 2-norm, not in operator
  norm, so the lift does not descend through the twisted presentation ideal.
  Turning this free lift into a ucp lift on the quotient generator system is
  precisely the remaining seam.
- Full LLP of `A_alpha` proves the claim, but
  `sp4-mod3-twisted-fibres-have-llp` is a stronger open problem.  A successful
  attack should use only the finite presentation and tracial 2-norm, avoiding
  arbitrary quotient algebras.
- Property (T) alone cannot correct arbitrary Choi/linear lifts to ucp lifts:
  `property-t-alone-cannot-correct-tracial-choi-lifts` applies such a
  hypothetical correction to Thom's hyperlinear Kazhdan group without the
  factorization property.  Any correction here must use the Deligne
  multiplier or symplectic arithmetic, not only a Kazhdan pair.
