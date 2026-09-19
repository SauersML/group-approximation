---
rg: 2
id: projective-transfer-gives-universal-filtered-actuator
kind: route
title: Projective commutant transfer gives one universal type-filtered wandering actuator
target: type-filtered-proper-corner-return-actuator
requires:
  - projective-trace-square-transfer-for-sl3-pair
  - one-filtered-wandering-return-is-already-nonhyperlinearity
  - residually-finite-models-refute-filtered-wandering-return
---

This is a proved reduction, conditional only on the displayed projective
transfer modulus.

It differs from `nonhyperlinear-from-projective-trace-square-transfer`,
which uses the modulus of one ordinary word trace directly: here one free
commutator cancels the unknown scalar phase and produces the positive
filtered-return interface.  It differs from the stronger
`thin-sln-robust-relative-commutant-transfer`, which tries to make the first
commutator itself close to the identity.

Let

```text
C=SL_3(Z) <= A=SL_3(Z[1/2]),
a=diag(2,1,1/2) in A-C.
```

Let `H` be any fixed finite context packet.  Form

```text
G_1=<H times A,t | [t,H]=1, [t,C]=1>,
Gamma=G_1 * <s>,                                      (PFA1)
```

using finite generating sets for `H` and `C`, and put

```text
v=[t,a],                 r=[v,s].                    (PFA2)
```

For **every** nonzero projection `P in C[H]`, the same word `r` has the
following properties.

### Normal form

Britton's lemma gives `v!=1`, because `a notin H times C`.  Free-product
normal form then gives

```text
g r !=1                  for every g in H.            (PFA3)
```

Indeed `g v` is a nontrivial element of `G_1`, and
`(g v)s v^(-1)s^(-1)` is reduced.  Thus every support word in `P r` is
wandering.

### Finite-matrix return

At defect zero the return is unconditional.  In every exact
finite-dimensional unitary representation of `Gamma`, co-density gives

```text
rho(C)'=rho(A)'.                                       (PFA4a)
```

The HNN relations put `rho(t)` in the left side, so `rho(t)` commutes with
`rho(a)`.  Hence `rho(v)=rho(r)=I`, independently of the matrix assigned to
`s`.  Thus `r` is a nontrivial word killed by every finite-dimensional
unitary representation, and every packet filter has the exact return
`tr(P rho(r))=tr(P)`.  Only robustness under normalized-HS approximate
representations remains open.

Let `T,S` be the matrices assigned to `t,s`.  The HNN relators make `T`
almost centralize the fixed generators of `C`.  The projective transfer
claim gives a scalar `zeta in T` such that

```text
||[T,a(U)]-zeta I||_2 <= epsilon(delta),              (PFA4)
```

with `epsilon(delta)->0`.  Scalar phases disappear under a commutator, and
unitary invariance plus telescoping gives

```text
||r(U)-I||_2
 =||[T,a(U)] S [T,a(U)]^(-1)S^(-1)-I||_2
 <=2 epsilon(delta).                                 (PFA5)
```

After exactifying the fixed finite packet, `P(U)` is a projection.  Hence

```text
|tr(P(U)r(U))-tr(P(U))|
 <=2 epsilon(delta) sqrt(tr(P(U))).                   (PFA6)
```

Using `2 epsilon sqrt(x)<=x/2+2 epsilon^2` yields the required positive
return

```text
Re tr(P(U)r(U))
 >=(1/2)tr(P(U))-2 epsilon(delta)^2.                  (PFA7)
```

This is `(TFP1)` with `c=1/2`, simultaneously for all primitive type and
forbidden-selector filters in `H`.

To derive `(PFA4)` from the trace-square formulation, note that for a
unitary `W`

```text
min_(zeta in T)||W-zeta I||_2^2=2-2|tr(W)|
 <=2(1-|tr(W)|^2).                                   (PFA8)
```

### Exact completeness

Both extensions in `(PFA1)` are injective by Britton and free-product normal
form, so the original packet mark remains nontrivial in `Gamma`.  Any exact
perfect commuting packet representation extends by sending `A,t,s` to the
identity; on allowed support no forbidden return is demanded.

Therefore `projective-trace-square-transfer-for-sl3-pair` would not merely
prove its existing arithmetic HNN route: after one free phase-cancelling
letter it supplies the entire type-filtered proper-corner interface with one
universal word.  Conversely, by
`one-filtered-wandering-return-is-already-nonhyperlinearity`, proving
`(PFA7)` for even one nonzero `P` is already the terminal breakthrough.  The
remaining open content is exactly the matrix-outlier part of projective
commutant transfer, not Bass--Serre normal form or packet filtering.
