---
rg: 2
id: extended-prefix-relative-word-centralizes-quarter-source
kind: claim
title: The extended asymmetric prefix conjugator differs from the native braid by a nontrivial fixed-source centralizer
artifacts:
  - research/extended-asymmetric-prefix-relative-source-proof.md
  - experiments/asymmetric_prefix_relative_source_audit.py
distinct_from:
  asymmetric-prefix-unit-conjugates-native-whiteheads: that constructs the first asymmetric-unit conjugator and records only its moved source; this extends the diagonal on the third native coordinate and identifies the entire relative word on every generator of the full quarter source.
  asymmetric-prefix-unit-misses-fixed-hecke-frame: that fences every diagonal extension of the original coordinate cycle from directly normalizing the fixed source; this factors one distinguished extension through the native braid and proves that its residual prefix unit is a nontrivial fixed-source centralizer.
  full-q-relative-word-hecke-interface-has-zero-central-block: that studies the compressed relative word J1J2 in the finite twisted Hecke algebra; this is an exact binary-Leavitt coefficient calculation identifying the extra asymmetric-unit factor before compression.
---

**ESTABLISHED EXACT GAUGE FACTORIZATION.**  Retain the asymmetric prefix
unit

```text
u=s_00t_0+s_01t_10+s_1t_11,
u^(-1)=s_0t_00+s_10t_01+s_11t_1
```

and the coordinate cycle `P=(7 8 9)`.  Extend the previous diagonal word by

```text
D~=h_(8,10)(u) h_(7,11)(u) h_(9,12)(u^(-2)),
G~=P D~.                                                   (EAR1)
```

Put

```text
A=J_1J_2,                  R=A^(-1)G~.                    (EAR2)
```

Then `G~J_1G~^(-1)=J_2`, just as for the shorter asymmetric conjugator.
More strongly, `G~` and `A` have exactly the same conjugation action on all
ten displayed generators of the signed group `L_0` and on the two extra
quarter-source signs

```text
r=x_58(a_2),                 l=x_69(a_3).                (EAR3)
```

Consequently

```text
[R,L_0]=[R,r]=[R,l]=[R,J_1]=1.                           (EAR4)
```

In particular, for

```text
Q=e_(L_0,lambda_0),          F=Q(1+r)(1+l)/4,
```

one has

```text
RF=FR,
G~FG~^(-1)=AFA^(-1).                                    (EAR5)
```

The factor `R` is not the identity: in the elementary image it retains the
diagonal entry `u^(-1)` on spare coordinate `10`, whereas `A` is supported
on coordinates `7,8,9`; also `u!=1` because `us_0=s_00`.  Thus extending the
third diagonal does not cancel the asymmetric prefix gauge.  It isolates it
as a genuine nontrivial fixed-source centralizer, while the moved-source
part of `G~` is exactly the already known native braid `J_1J_2`.

This is a sharp occurrence fence.  It does not assert that `R` survives in
every finite-dimensional representation, nor does it refute positive
cross-Gram mass for another authenticated transport.  It shows only that
this natural extended prefix conjugator supplies no new fixed-source
identification: after the native braid is removed, the remaining factor is
an uncontrolled source-centralizing gauge.

No Property `(T)`, canonical trace, or literature theorem is used.  The
faithful prefix-normal-form replay is run only through MSI.

DERIVATION
extended-asymmetric-prefix-relative-source-proof
