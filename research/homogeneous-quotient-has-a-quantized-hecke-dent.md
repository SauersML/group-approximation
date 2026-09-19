---
rg: 2
id: homogeneous-quotient-has-a-quantized-hecke-dent
kind: claim
title: The homogeneous quotient leak has a quantized one-shell Hecke dent which survives Morita amplification
artifacts:
  - research/homogeneous-quotient-hecke-dent-quantization-proof.md
distinct_from:
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that proves the orbit symmetry is moved and conditionally transports it into matrices; this gives an explicit finite lower bound for the single-shell norm dent before any embeddability assumption.
  single-hecke-dent-is-the-expanding-commutator-defect: that sandwiches the dent by the expanding commutator in an arbitrary finite tracial model; this quantizes that commutator for the compact homogeneous quotient using common-parahoric orbit counting.
  dense-s-arithmetic-translation-algebra-is-amplified-profinite: that gives the stable crossed-product presentation of the homogeneous algebra; this proves that passing to its standard finite Morita amplifications preserves, rather than dilutes, the leak.
---

Use the homogeneous-quotient notation

```text
A=SL_3(Z[1/p]), C=SL_3(Z), G=SL_3(Q_p), K=SL_3(Z_p),
X=G/Lambda', M=L^infinity(X) rtimes A,
h=diag(p,1,p^(-1)).
```

Let `P` be one `K`-orbit in `X`, let `r=|K\X|`, and put

```text
U=1-2 . 1_P,
D=[K:K cap hKh^(-1)]=p(p+1)(p^2+p+1).
```

For the lazy `D`-branch Hecke average `S` of
`single-hecke-average-isometry-for-lambda-central-unitaries`, one has

```text
||Ad(u_h)(U)-U||_2^2 >= 8/(rD),                        (HQD1)
1-||S(U)||_2^2 >= 2/(rD).                              (HQD2)
```

At the dyadic pair, `D=42`, so the dent is at least `1/(21r)`.

Moreover every normalized finite Morita amplification retains the same
numbers.  In `M tensor M_m`, with normalized trace and

```text
pi_m(a)=u_a tensor I_m,       U_m=U tensor I_m,
```

one has

```text
||Ad(pi_m(h))(U_m)-U_m||_2=||Ad(u_h)(U)-U||_2,
1-||S_m(U_m)||_2^2=1-||S(U)||_2^2.                     (HQD3)
```

Thus canonical regular trace, factoriality, an embeddable profinite
`C`-restriction, and arbitrary standard finite Morita amplification do not
force the expanding defect to vanish.  The remaining load-bearing question
is exactly whether the full homogeneous crossed product embeds into a matrix
ultraproduct.  Stabilizing the translation algebra cannot wash the leak out:
under `(DT2)`, every finite-rank standard corner contains the amplified
witness `(pi_m,U_m)` with the same normalized defect.

DERIVATION
homogeneous-quotient-hecke-dent-quantization-proof
