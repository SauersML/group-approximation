---
rg: 2
id: reverse-mixed-root-has-two-positive-hecke-commutator-returns
kind: claim
title: The reverse mixed-braid root has two positive-Hecke commutator returns, both spectator-typed
distinct_from:
  actual-mixed-complement-returns-reverse-root: that produces the bare nonnormal reverse root `x_97(1)`; this continues that literal occurrence through positive-character roots of `L_0` and returns to the signed Hecke carrier.
  signed-hecke-normalizer-has-eight-external-root-returns: that classifies all constant-root normalizers and realizes them through generic spare-coordinate inverse pairs; this realizes two of them by commutators containing the actual mixed-braid reverse-root occurrence.
  eight-external-returns-have-no-whitehead-gauge-lock: that exhausts the native Whitehead action on all eight external returns; this identifies exactly which two external returns arise from the reverse mixed root and applies that typing fence.
---

**ESTABLISHED POSITIVE RETURN WITH A SPECTATOR FENCE.**  Let

```text
X=x_97(1)                                             (RMR1)
```

be the literal output of the actual complementary mixed braid `(ACM4)`.
Two positive-character generators of the signed Hecke group are

```text
h_1=x_76(1),                 h_2=x_29(1).             (RMR2)
```

The ordinary nonopposite Steinberg commutator law gives

```text
[X,h_1]=x_96(1)=N_1,
[h_2,X]=x_27(1)=N_2.                                  (RMR3)
```

Both `N_1,N_2` occur in the exact external-normalizer list `(ERN2)`.
Since `h_1,h_2` lie in the positive kernel of `lambda_0`, the three-letter
continuations

```text
R_1=Xh_1X=N_1h_1,             R_2=Xh_2X=N_2h_2       (RMR4)
```

normalize the signed pair `(L_0,lambda_0)`.  On the signed Hecke carrier
`Q`, each `h_i` acts as the identity, so the returned occurrence `R_i` has
exactly the same compressed action and reservoir gauge as `N_i`.  Thus the
actual reverse root does have a short coefficient-free return to `Q`; the
failure `(ACM5)` is a failure of the bare root, not of every continuation.

These two returns do not reach the native target.  The complete native
orbit audit `(EWO3)` identifies

```text
N_1=x_96(1)  as fixed by J_1 and t_1,
N_2=x_27(1)  as fixed by J_2 and t_2.                 (RMR5)
```

In each row the external root is disjoint from the active Whitehead
coordinate pair.  Its apparent commutation square compares different
source and target multiplicity charts and gives only

```text
G_(k+1)=D_k G_k D_k^(-1),                             (RMR6)
```

not a same-chart relation `[D_k,G_k]=1`.  The exact finite `S_3`
moving-stage model of `eight-external-returns-have-no-whitehead-gauge-lock`
therefore retains the native Whitehead gauge while satisfying `(RMR3)--(RMR6)`.

Accordingly `(RMR3)` is a new authenticated signed-source return from the
actual mixed-braid occurrence, but it is spectator-typed and supplies
neither the source-to-native full Gram nor the gauge lock required by
`el20-six-moving-coefficient-square-bridges`.  A useful continuation must
make `X` return through an external normalizer meeting the active native
packet, or add a second relation which identifies one of the two spectator
gauges on the same chart.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation or Lean compilation is used.

DERIVATION
reverse-mixed-root-positive-hecke-return-proof
