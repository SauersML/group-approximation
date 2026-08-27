---
rg: 2
id: three-root-asymmetric-kl-word-has-finite-core-pushout
kind: claim
title: The minimal asymmetric three-root Leavitt equation is a finite-core Bass-Serre pushout and preserves the coefficient group
distinct_from:
  two-root-two-block-kl-word-is-cyclic-amalgam: That two-block word folds by one Tietze substitution to a cyclic root adjunction; this three-block word has sign pattern plus-plus-minus and does not so fold, but fails because all coefficients localize to a finite hyperlinear subgroup.
  leavitt-degree-kernel-quotient-tests-are-procyclic: That constrains finite quotients of the degree kernel; this computes the full relative quotient as an amalgam over a finite coefficient subgroup.
  leavitt-degree-kernel-normally-generated-by-one-word: That asks for a successful degree-kernel normal generator; this rules out the minimal asymmetric adjacent-root candidate explicitly.
artifacts:
  - research/artifacts/verify-three-root-asymmetric-kl.py
---

Inside `G=L_(F_2)(1,2)^x ~= EL_20(R)`, take the constant adjacent-cycle
roots

```text
r=x_12(1),       s=x_23(1),       v=x_31(1).
```

Each is a nontrivial involution and normally generates `G`; together they
generate the finite constant subgroup

```text
H=EL_3(F_2)=GL_3(F_2),       |H|=168.
```

Consider the minimal asymmetric three-block word

```text
w=r t s t v t^(-1),          deg_t(w)=1.                (TAK1)
```

Its coefficient-depth/Fox pattern is `(0,1,2)`:

```text
w = r (t s t^(-1)) (t^2 v t^(-2)) t.                   (TAK2)
```

The exact `168`-matrix enumeration in the artifact shows that `(TAK1)` has no
solution `t in H`, for any of the three placements of the unique negative
variable occurrence.  Nevertheless, if

```text
P_H=(H*<t>)/<<w>>,       P_G=(G*<t>)/<<w>>,
```

then

```text
P_G ~= G *_H P_H,                                          (TAK3)
```

and both vertex groups embed.  Indeed `H` is finite, hence hyperlinear, so
Kervaire--Laudenbach holds over `H` and the natural map `H->P_H` is injective.
Bass--Serre normal form applied to `(TAK3)` then embeds `G` in `P_G`.

There is also a stronger coefficient-independent reason this candidate could
never work: its variable length is three, so
`length-five-kl-fence-for-leavitt-equations` injects `G` directly.  The
finite-core pushout remains useful because it identifies the quotient's exact
Bass--Serre structure and explains why failure persists despite the absence
of a solution inside `H`.

Thus `w` does not normally generate `N_1=G*<t>`.  The obstruction is not a
cyclic root fold and not visible by substituting an element of the coefficient
core itself: it is the exact finite-core pushout.  More generally, no
candidate whose coefficients lie in a finite (or otherwise known
Kervaire--Laudenbach) subgroup can work.  A viable Leavitt candidate must use
a finite coefficient set generating a subgroup for which nonsingular
coefficient injectivity is itself unresolved—in particular, the constant
root packets and finite prefix-transposition packets are excluded.
