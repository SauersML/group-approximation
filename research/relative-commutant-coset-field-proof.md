---
rg: 2
id: relative-commutant-coset-field-proof
kind: route
title: Quotient by the exact stabilizer action and conjugate prototypes
target: relative-commutant-coset-field-removes-stabilizer
requires: []
---

If `hK=h'K`, write `h'=hk`.  Exactness of `V` and
`[A_0,V(k)]=0` give

```text
V(h')A_0V(h')^*=V(h)V(k)A_0V(k)^*V(h)^*=V(h)A_0V(h)^*.
```

Thus `(RCF1)` is well-defined.  For `g in H`,

```text
A_(ghK)=V(g)A_(hK)V(g)^*.                                (RCF2)
```

Let `r` be a fixed noncommutative word in lamps at a finite tuple of cosets.
Equation `(RCF2)` says that evaluation on a common `g`-translate is
`V(g)r(A)V(g)^*`.  Unitary invariance of normalized Hilbert--Schmidt norm
makes its defect identical to the prototype defect.  If the prototype
entries are changed by at most `C delta`, telescoping the fixed word costs at
most `|r| C delta`; its translate costs exactly the same.

This compares corrected prototypes and contextual conjugates.  Comparing
`V(h)A_0V(h)^*` with a raw word `U(h)AU(h)^*` additionally requires control
of `U(h)-V(h)`, which can grow with transporter length and is not a
consequence of the lemma.

