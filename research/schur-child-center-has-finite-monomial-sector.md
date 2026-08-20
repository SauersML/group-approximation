---
rg: 2
id: schur-child-center-has-finite-monomial-sector
kind: claim
title: The corrected Schur child center is a literal element in one finite irreducible monomial sector
distinct_from:
  finite-predicate-signed-permutation-sector: that realizes an arbitrary spectral support with no prescribed packet action; this simultaneously contains the Schur packet restriction and its corrected child-center operator.
  groupify-schur-child-center-chart: that must control every approximate representation of the eventual presentation; this constructs only one exact finite irreducible sector.
---

For every fixed Schur packet `B_f` there is a finite signed-permutation group
`H_f`, an embedding `iota:B_f->H_f`, an element `r_f in H_f`, and an
irreducible finite-dimensional representation `pi_f` of `H_f` such that:

1. the common packet sign satisfies `pi_f(iota(J))=-I`;
2. as a `B_f`-module, `pi_f` contains every `J=-1` packet simple with positive
   finite multiplicity; and
3. on each selector sector, `pi_f(r_f)` equals the corrected involution `Q_x`
   of `(SCP4)`. Hence its two signs give exactly the two `Q`-child types.

Thus the additive formula `Q_f=sum_x e_xQ_x` can be made a literal group
element inside one selected finite irreducible sector. The obstruction is not
local existence. It is sector soundness: an arbitrary representation of
`H_f` need not be a sum of copies of `pi_f`, so group relations alone do not
yet force `r_f` to retain this meaning.
