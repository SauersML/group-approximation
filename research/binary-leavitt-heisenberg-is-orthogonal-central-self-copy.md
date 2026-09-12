---
rg: 2
id: binary-leavitt-heisenberg-is-orthogonal-central-self-copy
kind: claim
title: A binary Leavitt Heisenberg group is the central product of two commuting self-copies
distinct_from:
  finite-root-heisenberg-multiplicity-germs: that extracts exact finite additive and multiplicative rank germs from matrix-corona root windows; this is an exact algebraic decomposition of the full Heisenberg group before any approximation.
  iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart: that identifies the full coefficient ring with its depth-n prefix matrix chart; this identifies the induced orthogonal self-copies of the three-root Heisenberg group and their common center.
artifacts:
  - research/binary-leavitt-heisenberg-central-self-copy-proof.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**ESTABLISHED.** Let `R` carry a binary Leavitt family

```text
t_i s_j=delta_ij,                  s_0t_0+s_1t_1=1.
```

Write `H(R)=R^3` with

```text
(a,b,c)(a',b',c')=(a+a',b+b',c+c'+ab').               (HSC1)
```

For `i=0,1`, define

```text
alpha_i(a,b,c)=(a t_i,s_i b,c).                        (HSC2)
```

Then each `alpha_i` is an injective homomorphism, the two images commute,
their intersection is the central subgroup

```text
Z_0={(0,0,c):c in R},
```

they generate `H(R)`, and both maps fix `Z_0` pointwise.  Thus `H(R)` is the
internal central product of the two self-copies.  At depth `n`, the same
construction gives `2^n` mutually commuting copies with common intersection
`Z_0` and generated product all of `H(R)`.

If `R` is an algebra over a finite field, then `H(R)` is locally finite.
In particular the binary-Leavitt Heisenberg subsystem over `F_2` is MF even
though it has exact orthogonal self-copy at every depth.  The abstract
three-root self-similarity is therefore not the missing MF obstruction; a
return to the same finite matrix atom is additional structure.

