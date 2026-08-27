---
rg: 2
id: selector-product-is-a-payload-corner-square-root
kind: claim
title: The one-bit selector product is a literal payload-corner square root
distinct_from:
  one-bit-clifford-selector-halves-a-chosen-bcs-atom: that uses one selector spectral half only as positive mass; this uses the ordered product of both selector involutions as an odd phase-sensitive word.
  schur-flip-square-exposes-payload-root-word: that cancels two Schur packet flip implementers and obtains the actual external multiplicity holonomy; this gives a much smaller BCS-corner square root but not its incidence with a Schur return.
  fresh-central-square-lift-is-extension-trivial: that adjoins an unrelated square-root generator; this word is fixed by the selected assignment and has an explicit global structural square.
---

**ESTABLISHED LOCAL RAW-PHASE WORD; RETURN INCIDENCE REMAINS OPEN.**  Fix a
context assignment `a`, a variable `v in c`, and use the one-bit selector
involutions `p_a,q_a` with

```text
[p_a,q_a]=r_a:=J^(1-a(v))x_v.                          (SQR1)
```

Since the selector letters are involutions, the literal ordinary word

```text
d_a=p_a q_a                                             (SQR2)
```

satisfies

```text
d_a^2=r_a.                                              (SQR3)
```

Let

```text
h_(a,v)=x_v J^(a(v)) in H_a,
E_a=P_(c,a)(1-J)/2.                                    (SQR4)
```

The selector commutes with the context packet, `h_(a,v)E_a=E_a`, and the
global word identity is

```text
d_a^2 h_(a,v)=J.                                       (SQR5)
```

Consequently `d_a` preserves the selected payload carrier and

```text
E_a d_a^2=J E_a=-E_a.                                  (SQR6)
```

Thus `E_ad_aE_a` is a raw, phase-sensitive square root of the marked sign on
the actual forbidden atom.  This is not merely a projective `PGL` class.
Multiplication by any element of `H_a` changes the global lift without
changing its compression to `E_a`, making explicit the off-payload gauge.

All formulas are dimension-independently robust after fixed context/selector
packet correction: normalized-HS error in `(SQR6)` is bounded by a fixed
constant times the square root of the selector, involution, commutation, and
context-relator energy.  This follows by word telescoping and compression by
the corrected Reynolds atom.

The exact perfect tracial model is consistent.  Use the Pauli realization
from `one-bit-clifford-selector-halves-a-chosen-bcs-atom`; every forbidden
`P_(c,a)` is zero, so the corner condition is vacuous, while `(SQR3)--(SQR5)`
hold globally and `J` remains nontrivial.

This removes the **local phase** obstruction but does not by itself prove the
binary Schur payment.  Tensor the exact selector packet with the stationary
equal-child Schur model of
`binary-schur-canonical-weights-have-half-reservoir-escape`.  Every selector
row, including `(SQR5)`, is exact and `E_a` may have positive trace, while the
two Schur children retain equal multiplicity and neither exit is paid.  Hence
no estimate `(BHP2)` follows until an ordinary relation makes the compressed
word `E_ad_aE_a` the **actual relative holonomy of the Schur return on that
same proper source**.

A full-carrier identification is not the missing relation:
`projective-gauge-charge-forces-morita-or-corner` shows that a charged
intertwiner between equal full child carriers generates the branch Morita
`M_2` and consumes the surplus.  The surviving interface is exactly a
payload-compressed proper-corner incidence.  The selector word supplies its
square root; it does not authenticate that incidence.

There is also a sharp global-completeness obstruction to identifying this
word directly with the coefficient Whitehead payload word.  In the perfect
model `B_f=0`, so the Whitehead word is one.  A global relation

```text
W_(B_f)=d_a h,              h in H_a                   (SQR7)
```

would therefore force `d_ah=1`.  But `d_a` commutes with `H_a`, every
`h in H_a` is an involution, and

```text
(d_a h)^2=d_a^2=r_a.                                  (SQR8)
```

Thus `(SQR7)` forces the literal structural word `r_a` to be one in the
perfect representation.  The same conclusion follows from the weaker
square identification `W_(B_f)^2=d_a^2`.  If the chosen perfect BCS trace has
a nonzero `r_a=-1` sector, exact completeness is destroyed.  If it does not,
then `r_a=1` is already the residual ordinary packet detector isolated by
`load-bearing-hnn-substitution-is-an-ordinary-packet-detector`; the
Whitehead/selector amalgam has not manufactured payload sensitivity.

Hence the useful statement is genuinely **corner-local** `(SQR6)`.  Promoting
it to a global cyclic amalgam either fails completeness or reduces to a
pre-existing literal packet relation.

DERIVATION
selector-product-payload-square-proof
