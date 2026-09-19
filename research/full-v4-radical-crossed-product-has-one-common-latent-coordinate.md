---
rg: 2
id: full-v4-radical-crossed-product-has-one-common-latent-coordinate
kind: claim
title: The full V4 radical crossed product synchronizes all three S3 chart labels
distinct_from:
  three-radical-twist-crossed-products-have-uniform-scale: that adjoins one radical translation at a time and obtains two chart blocks; this adjoins both independent translations simultaneously and classifies their common refinement.
  same-context-s3-endpoint-atlas: that must additionally realize the diagonal/crossed success laws; the present finite group supplies one common latent radical coordinate but no law declaring any of its atoms erroneous.
  finite-projective-v4-holonomy-is-forbidden-sector-blind: that varies the scalar two-cocycle of the two translation lifts and proves that this cannot supply the missing endpoint law.
---

Let `K_f` be the phase-root packet of
`every-predicate-has-s3-equivariant-raw-radical-drop`, and retain the two
independent central-twist automorphisms `tau_1,tau_2` from `(RTC2)`.  They
commute, and `tau_3=tau_1 tau_2`.  Form the finite semidirect product

```text
T_f=K_f semidirect <s_1,s_2>,
<s_1,s_2> isomorphic to V_4,
s_i g s_i^(-1)=tau_i(g).                              (VRC1)
```

Write `D_0=2^(2N)` as in `(RTC1)`.  In a forbidden selector sector, the
`K_f` algebra is the direct sum of four copies of `M_(D_0/2)`, indexed by
the radical characters

```text
r in R=F_2^2.                                          (VRC2)
```

The quotient `V_4` acts on these four summands by all translations of `R`.
The action is free and transitive.  Therefore the sector algebra of `T_f`
is the single full matrix algebra

```text
M_(4(D_0/2))(C)=M_(2D_0)(C).                           (VRC3)
```

Let `R_i=K_f semidirect <s_i>` for `i=1,2`, and use
`R_3=K_f semidirect <s_1s_2>`.  Each forbidden `R_i` sector is the two-block
algebra in `(RTC4)`.  The unique simple module in `(VRC3)` restricts to

```text
one copy of each of the two simple R_i modules.          (VRC4)
```

Indeed, its restriction to `K_f` contains each of the four radical simples
once.  An `R_i` simple contains exactly the two `K_f` simples in one orbit
of translation by the corresponding nonzero vector.  The two orbits
partition `R`, so dimension and `K_f` type content force `(VRC4)`.

Consequently every finite-dimensional `T_f` module has one common latent
radical decomposition for all three charts.  If the two coordinates of
`r` are `(u,v)`, the three quotient labels can be chosen as

```text
b_1=v,             b_2=u,             b_3=u+v.          (VRC5)
```

Their common support is exactly

```text
{000,011,101,110},                                     (VRC6)
```

and all four atoms have equal multiplicity on each forbidden `T_f` simple.
Thus the full crossed product repairs the former pairwise-coupling gap: the
three chart labels are functions of one and the same `r`, rather than three
independently chosen bistochastic couplings.

For completeness, a satisfying selector sector has one `K_f` block
`M_(D_0)`, fixed by `V_4`.  Choose inner implementers `U_1,U_2` of the two
automorphisms on this block.  Their scalar commutator determines a Mackey
class in `H^2(V_4,T)`.  The satisfying sector algebra is accordingly either

```text
M_(D_0)(C) direct_sum ... direct_sum M_(D_0)(C)          (four summands)
```

or

```text
M_(2D_0)(C),                                             (VRC7)
```

according as that class is trivial or nontrivial.

This theorem supplies common-latent synchronization, but it does **not**
prove local payment.  The finite group `(VRC1)` has exact representations on
every forbidden sector, and all three translations act exactly there.  A
separate relation must still turn the affine labels `(VRC5)` into the
diagonal/crossed success conventions.  The point of `(VRC1)--(VRC6)` is that
this remaining relation may now be sought on one common multiplicity space;
the no-signaling-box escape is no longer the relevant obstruction.

