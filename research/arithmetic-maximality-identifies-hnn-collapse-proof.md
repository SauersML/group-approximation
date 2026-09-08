---
rg: 2
id: arithmetic-maximality-identifies-hnn-collapse-proof
kind: route
title: Combine Smith maximality with tensor stabilizer extraction and the arithmetic transfer theorem
target: arithmetic-hnn-nonhyperlinearity-equals-global-collapse
requires:
  - smith-prime-localization-maximality-and-word-transfer
  - maximal-subgroup-hnn-equals-commutant-collapse
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
  - rf-perfect-pair-transfer-equals-regular-rcc
  - kazhdan-rcc-has-prescribed-projective-transfer-slope
---

Smith maximality proves that `C` is a maximal proper subgroup of `A`
for every stated rank and prime. The maximal-subgroup theorem then
gives `1 iff 2`. The general coset equivalence gives `1 iff 3 iff 4
iff 5`.

A canonical hyperlinear HNN model has a Haar stable letter `t`.
Britton reduction gives
`tau(t* u_g t u_g*)=1_C(g)`, proving that failure of 1 implies failure
of 6. Conversely a witness forbidden by 6 is a commutant leak because
`C<A` and its outside coefficient is zero. Thus 2 implies 6. Together
with `1 iff 2`, this proves the full six-way equivalence without
assuming that this particular unitary is an involution or has any
additional free moments.

For `n>=3`, the arithmetic actor is residually finite, finitely
presented, and perfect, and `C` is finitely generated and perfect.
These are the arithmetic hypotheses checked by
`rf-perfect-pair-transfer-equals-regular-rcc`. Maximality also proves
`A=<C,h>` since the displayed denominator diagonal lies outside `C`.
That theorem gives the final linear inequality exactly. Its linear
form implies the older formulation with an arbitrary defect modulus;
the older formulation implies canonical RCC by its zero-defect limit
and perfectness (or by adjoining an identity witness block). Hence the
formulation in `projective-trace-square-transfer-for-sl3-pair` is
equivalent as well. No such perfect-pair assertion is used in rank two.

For the prescribed coefficient, `n>=3` supplies property (T) of `C`,
while residual finiteness gives hyperlinearity of `A`. Apply
`kazhdan-rcc-has-prescribed-projective-transfer-slope` to obtain the
equivalent inequality with `K=4/kappa^2` and a qualitative defect
modulus. This argument does not require either group's perfectness,
and does not assert an effective or linear modulus with this fixed K.
Its tensor amplification refinement gives a linear defect term for
every strictly larger subgroup-energy coefficient.
