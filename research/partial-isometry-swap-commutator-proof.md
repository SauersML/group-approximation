---
rg: 2
id: partial-isometry-swap-commutator-proof
kind: route
title: Compare one swap commutator with its two-sided Gram residual
target: partial-isometry-swap-wordizes-one-bcs-gram-row
requires: []
---

Let `S` be a partial isometry in a finite tracial matrix algebra, with
`P=SS^*` and `Q=S^*S`.  For self-adjoint unitaries `A,B`, set

```text
R=AS-SB,
J_S=[[I-P,S],[S^*,-(I-Q)]],
D=diag(A,B).
```

The partial-isometry identities `PS=S=SQ` show directly that
`J_S=J_S^*` and `J_S^2=I`.  Since `D^2=I`, multiplication by unitaries gives

```text
||D J_S D J_S-I||_2=||[D,J_S]||_2.                   (PSC1)
```

The additive commutator is

```text
[D,J_S]=[[[A,I-P],R],[-R^*,[B,Q]]].                  (PSC2)
```

With the normalized trace on the `2 by 2` amplification, the two
off-diagonal blocks in `(PSC2)` contribute exactly `||R||_2^2`.  This proves
the lower bound.  For the reverse bound, expanding `R` and `R^*` gives

```text
AP-PA=RS^*-SR^*,
BQ-QB=-R^*S+S^*R.
```

Each diagonal block therefore has `2`-norm at most `2||R||_2`.  Hence

```text
||R||_2^2
 <=||D J_S D J_S-I||_2^2
 <=(1/2)(4+1+1+4)||R||_2^2
 =5||R||_2^2.                                        (PSC3)
```

Thus the ordinary commutator word is exact exactly when `AS=SB`, with
dimension-independent constants.  Taking `A=I-2F_c`, `B=I` gives the
predicate row `-2F_cS`; taking the occurrence and global-variable
involutions gives the consistency row.  One common partial isometry therefore
wordizes every row in the fixed BCS Gram test without rank or dimension loss.
