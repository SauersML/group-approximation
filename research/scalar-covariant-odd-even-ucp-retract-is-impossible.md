---
rg: 2
id: scalar-covariant-odd-even-ucp-retract-is-impossible
kind: claim
title: Scalar-cochain covariance makes an odd-to-even ucp retract impossible
invalidates:
  - odd-maslov-llp-via-scalar-covariant-retract
distinct_from:
  finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres: that assumes a finite projective coefficient action and reads its cocycle class; this needs no a priori multiplicativity and derives it from scalar-line covariance plus the split ucp norm equality.
  odd-maslov-ucp-retract-must-hide-generator-defect: that rules out faithful retractions but leaves positive-kernel hiding open; this proves that scalar covariance itself prevents any such hidden defect.
  v4-twisted-fibre-has-a-nonfaithful-untwisted-matrix-retract: that non-equivariant countermodel uses state-valued extra coordinates; this shows why forcing every generator into its canonical scalar homogeneous line kills that escape.
---

**ESTABLISHED SHARP COVARIANCE NO-GO.**  Let `A_alpha` be an odd Maslov
fibre (`alpha=1/3,2/3,1/6,5/6`) and `A_epsilon` an even fibre
(`epsilon=0,1/2`).  Fix a finite canonical generating set `Sigma`.  There do
not exist ucp maps

```text
i:A_alpha -> M_n(A_epsilon),       r:M_n(A_epsilon)->A_alpha,
r i=id,                                                     (SCR1)
```

such that, for every `s in Sigma`,

```text
i(u_s^alpha)=c_s (I_n tensor u_s^epsilon)                  (SCR2)
```

for some scalar `c_s`.  The scalars need not be assumed unimodular and need
not initially satisfy a cochain identity.

Indeed the split ucp norm equality forces `|c_s|=1`.  Thus every image in
`(SCR2)` is unitary, all canonical generators enter the multiplicative
domain of `i`, and `i` becomes a star-homomorphism.  Composing with a
finite-dimensional representation of the even fibre produces the forbidden
finite-dimensional odd projective representation.

So exact covariance **modulo a scalar cochain** is already too strong.  The
weakest surviving canonical covariance must allow genuinely nonscalar matrix
coefficients on at least one generator.  Exact coaction/homogeneous
covariance with such matrix coefficients does not suffice, as shown by
`matrix-homogeneous-ucp-retracts-can-hide-defect`.

The proof is `scalar-covariant-retract-multiplicative-domain-proof`.


