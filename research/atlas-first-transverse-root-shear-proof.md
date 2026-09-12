---
rg: 2
id: atlas-first-transverse-root-shear-proof
kind: route
title: Diagonalize the two adjacent root subgroups and compute the Steinberg shear
target: atlas-first-transverse-root-shear-leaves-fixed-character-face
requires:
  - atlas-ck-dual-pair-cell-leaves-one-partition-multiplicity
  - atlas-steinberg-rank-five-translation
  - atlas-steinberg-spare-index-independence
---

The literal rows `st3_123_a1` are exactly

```text
[x_12(a),x_23(1)]=x_13(a).                             (TSR1)
```

All roots have order two.  The (St2) relation makes `x_13(a)` commute with
both `x_12(b)` and `x_23(1)`, for every `a,b`; same-root additivity makes
each of the `12` and `13` families abelian.  From

```text
C_a T C_a T=D_a
```

and centrality of `D_a`, multiplication by `C_a` gives
`T C_a T=C_aD_a`.  This proves `(TRS3)`.

For a finite coefficient set, its joint spectral projection is

```text
Q_(chi,eta)
 = product_a ((1+chi_a C_a)/2) ((1+eta_a D_a)/2).      (TSR2)
```

Conjugating each factor by `T`, using `(TRS3)`, replaces `chi_a` by
`chi_a eta_a` and fixes `eta_a`.  This proves `(TRS4)` and the orbit
classification.

Spare-index independence defines `C_p,C_q,D_p,D_q` for the length-two
monomials.  The same Steinberg calculation applies to these derived roots.
The partition relation gives `C_pC_q=Z` and `D_pD_q=W`.  Therefore

```text
T Z T = ZW,
T C_p T=C_pD_p,
T C_q T=C_qD_q.                                       (TSR3)
```

If `W=+1`, the marked sign of `Z` is preserved and `eta_p=eta_q`.  The
common negative sign flips both `C_p,C_q`, exchanging the two complementary
negative cuts; the common positive sign fixes both.  If `W=-1`, `(TSR3)`
flips the sign of `Z`.  These are exactly the three cases stated in the
claim.

The fixed-face model is obtained by setting every `D_a` and `T` to the
identity.  It satisfies `(TSR1)` because every right-hand side is then the
identity.  It is deliberately only a representation of this transverse
subsystem.  Its purpose is to prove that no consequence of the five rows
`st3_123_a1` alone can remove their fixed face; other Atlas roots must do
that work.
