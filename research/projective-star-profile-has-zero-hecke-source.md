---
rg: 2
id: projective-star-profile-has-zero-hecke-source
kind: claim
title: The literal projective head has a marked-star profile with zero full-Hecke source
artifacts:
  - research/projective-natural-source-separation-proof.md
  - experiments/full_q_source_mass_natural_profile_audit.py
distinct_from:
  full-q-a1-projective-head-is-a-literal-finite-subgroup: that identifies the A1-extended head faithfully with a finite binary group; this uses its containing literal SL7 head to separate the marked-star carrier from the full-Hecke character source.
  literal-a1-head-forces-arbitrary-profile-native-cross-gram: that gives a uniform target-cross floor conditional on positive full-Hecke source F; this proves that positive marked-star mass does not imply that source hypothesis by finite-head central support.
  seventeen-root-star-has-marked-triple-overlap: that forces positive mass on the three-root carrier in every surviving full-group profile; this is a finite-head profile fence and is not asserted to extend to the full Steinberg group.
---

**ESTABLISHED FINITE-HEAD SOURCE FENCE.**  In the literal finite subgroup

```text
Phi(SL_7(F_2)) < St_20(L_(F_2)(1,2)),
```

retain the A1 head notation

```text
K=<L_0,r,l>,
F=|K|^(-1) sum_(k in K) chi(k)k,
C_1=x_42(q),
E=product_(i=1)^3 (1-D_i)/2,
(D_1,D_2,D_3)=(x_42(q),x_52(q),x_62(q)).             (PNS1)
```

There is an exact complex permutation representation `pi_7` of this literal
`SL_7(F_2)` on the `127` nonzero vectors of `F_2^7` such that

```text
rank pi_7(F)=0,
rank pi_7((1-C_1)/2)=32,
rank pi_7(E)=8.                                        (PNS2)
```

Consequently, in both `C[P_A]` and
`C[Phi(SL_7(F_2))]`,

```text
(1-C_1)/2 notin C[G] F C[G],
E           notin C[G] F C[G].                        (PNS3)
```

Thus neither the direct marked-to-`C_1` overlap nor the positive
three-root-star carrier can pay the positive-source hypothesis of the
literal A1 cross-Gram theorem using only central support in the finite
projective head.  Enlarging from `P_A` to the full literal `SL_7(F_2)` head
does not repair this source seam.

The fence persists after adjoining the mark itself.  Add the two projective
summands `q@1,q@3` to the seven active summands.  The same projective
matrix-unit construction gives a literal

```text
Phi_9(SL_9(F_2))<Delta
```

containing the projective head and `z=x_13(q)`.  In its permutation
representation `pi_9` on the `511` nonzero vectors of `F_2^9`,

```text
rank pi_9(P_z)=128,       rank pi_9(F)=0,
rank pi_9(E)=32.                                       (PNS3a)
```

Thus even the finite projective head enlarged by the actual surviving mark
has a mark-positive and star-positive profile with zero full-Hecke source.
There is also an exact sign mismatch before choosing any profile:

```text
x_52(q)E=-E,              x_52(q)Q=+Q,
EQ=0,                     EF=0.                       (PNS3b)
```

The marked-root-star carrier therefore lies on the opposite derived-root
sheet from the fixed full-Hecke source.  A successful route cannot obtain
the latter merely by intersecting the former with `Q`.

The adjacent Whitehead product has maximal compression on the star carrier:

```text
rank pi_7(EJ_1J_2E)=8,
rank pi_9(EJ_1J_2E)=32.                                (PNS4)
```

Indeed `J_1,J_2` move only the three prefix summands and commute with the
three row roots defining `E`.  This does not contradict `(PNS2)`: the
full-Hecke source `F` is the occurrence which types the native compression
flags, and that source vanishes in both profiles.

This is a scoped finite-head obstruction, not a representation of the full
infinite Steinberg group and not a refutation of the arbitrary-profile
native cross-Gram theorem.  It says that the remaining positive-density
bridge must use a relation outside the literal projective `SL_7` head, or
must type the maximal `EJ_1J_2E` occurrence directly without passing through
`F`.  No Property `(T)`, canonical trace substitution, literature theorem,
or local computation is used.

DERIVATION
projective-natural-source-separation-proof
