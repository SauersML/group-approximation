---
rg: 2
id: literal-mf-radical-via-finite-packet-holonomy
kind: route
title: Box the literal exact radical using the eight-lamp common-carrier certificate
target: literal-mf-radical-is-unsquared-defect
requires:
  - finitely-presented-sofic-non-mf
  - literal-central-mark-corona-invisible
  - literal-mark-quotient-not-mf
  - literal-unsquared-defect-finite-packet-holonomy
  - literal-unsquared-defect-quotient-is-mf
  - universal-mf-quotient
artifacts:
  - research/artifacts/literal-eight-lamp-finite-packet-holonomy-2026-08-26.md
  - research/artifacts/literal-mf-radical-computation-2026-08-19.md
  - GroupApproximation/Sofic/LiteralTheoremAPackage.lean
---

Let `u=[tct^-1,v_1]` and `D=<<u>>^E`.  The literal group is finitely
presented and sofic by `finitely-presented-sofic-non-mf`.

For the hard inclusion, take an arbitrary corona homomorphism from `E`.
`literal-central-mark-corona-invisible` makes it factor through `E/<w>`, and
`literal-unsquared-defect-finite-packet-holonomy` kills the image of `u`
there.  Every kernel is normal, so

```text
D <= Rad_MF(E).
```

For the reverse inclusion, `literal-unsquared-defect-quotient-is-mf` gives a
faithful corona model of `E/D`.  Pulling it back along `E->E/D` produces a
corona representation with kernel exactly `D`, and hence

```text
Rad_MF(E) <= D.
```

Therefore

```text
BOXED:  E is finitely presented and sofic,
        Rad_MF(E) = <<[tct^-1,v_1]>>^E.
```

The affine parity computation also gives `D=N_conj`; the quotient claim gives
`E/D~=Sigma *_B(B x C_2)`, and `universal-mf-quotient` identifies this as the
maximal MF quotient.  This route is independent of the original
commuting-involution proof of the lower inclusion.

Finally `w=u^2`, so `<w><=D`.  Radical pullback through `q:E->E/<w>` gives
`Rad_MF(E/<w>)=D/<w>`.  The specific involutive collapse ideal `D_coll` from
`literal-mark-quotient-not-mf` contains the base commutators that normally
generate `D/<w>`, while the general collapse theorem puts `D_coll` inside
that radical.  Hence

```text
D_coll=Rad_MF(E/<w>)=D/<w>,
Rad_MF(E)=q^-1(D_coll).
```
