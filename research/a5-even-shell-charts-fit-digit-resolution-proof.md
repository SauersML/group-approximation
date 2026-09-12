---
rg: 2
id: a5-even-shell-charts-fit-digit-resolution-proof
kind: route
title: Double the single-ray charts and retain four residue roots for the exact shell permutations
target: a5-arithmetic-shell-envelope-embeds-in-fp-simple-group
requires:
  - a5-free-product-has-simple-arithmetic-shell-envelope
  - fixed-base-shells-embed-in-contracting-rsg
artifacts:
  - research/artifacts/boone-higman-terminated-digit-resolution-2026-09-08.md
---

Put h=59. The single-ray generator lambda_a has source modulus
2*h and image steps 2*h^2, 2*h, or 2. Its shell copy acts on
even indices by rho_a(2*n)=2*lambda_a(n), fixing odd indices.
Consequently on source residues modulo 4*h, its even branches
have image steps 4*h^2, 4*h, or 4, and its odd branches have
image step 4*h. These are precisely four-root odometer charts
with output depths 2,1,0, or 1, respectively. Bijectivity gives
the target prefix partition. The finitely many exceptions are
kept in the actual permutations, and inverses have the same form.

Thus the fixed-base lifting theorem applies with r=4 and h=59
to the actual rho generators of E_nu. It embeds E_nu in H_(59,4),
and that group embeds in a finitely presented simple group.

The earlier two-root model concerned lambda and the near group R.
Using four roots here is essential because this construction lifts
rho itself. No passage to the germ quotient discards finite errors
or the neighborhood kernel in this argument.
