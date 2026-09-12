---
rg: 2
id: higman-half-row-has-regular-mf-benign-witness
kind: claim
title: Higman's positive half-row has a finitely presented regular-MF benign witness
artifacts:
  - GroupApproximation/Higman/RowDeletionBenign.lean
distinct_from:
  mf-safe-asymmetric-hnn-replacement: that asks for MF control of the final graph HNN in the rope compiler; this proves MF control of the classical two-letter benign witness used earlier in the construction.
  mf-positive-controls: residual finiteness supplies the first tower only; the second tower is recognized as a central HNN extension by a Tietze change.
---

Let `F=<b,c>` and define injective endomorphisms

```text
xi_0(b)=b,             xi_0(c)=c^2,
xi_1(b)=c^-1 b c,      xi_1(c)=c^2.                    (HMF1)
```

The two-stage group in Higman's half-row witness is

```text
Gamma_0=<F,t_0 | t_0 x t_0^-1=xi_0(x), x in F>,
Gamma_1=<Gamma_0,t_1 |
          t_1 x t_1^-1=xi_1(x), x in F>.              (HMF2)
```

ESTABLISHED.  `Gamma_1` is finitely presented and regularly operator-MF.
Indeed, Borisov--Sapir residual finiteness of free-group mapping tori makes
`Gamma_0` residually finite.  Moreover

```text
xi_1(x)=c^-1 xi_0(x)c
```

for every `x in F`.  With

```text
z=t_0^-1 c t_1,        equivalently t_1=c^-1 t_0 z,   (HMF3)
```

the second family of relations in `(HMF2)` is exactly

```text
[z,x]=1, x in F.                                      (HMF4)
```

Thus a Tietze transformation identifies

```text
Gamma_1 ~= <Gamma_0,z | [z,F]=1>,                     (HMF5)
```

which is a central HNN extension of the residually finite group `Gamma_0`.
The regular central-HNN closure theorem applies.

The formal development `Higman/RowDeletionBenign.lean` proves that
`L=<b,t_0,t_1>` meets the base `F` in precisely the nonnegative half-row
`<c^-i b c^i : i>=0>` and transports this witness to the strictly positive
half-row.  Hence the classical finitely presented benign witness is not only
torsion-free: its ambient group is regularly operator-MF.
