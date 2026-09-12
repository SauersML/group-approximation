---
rg: 2
id: literal-selector-roots-force-center-chain
kind: claim
title: Literal native selector commutators force a noncommuting Pauli-center chain
distinct_from:
  marked-root-star-carries-three-anchored-cells: that keeps the three q-centers commuting by making every cross commutator trivial; this proves that exposing the two desired cross-products as the corresponding literal cross commutators destroys that common-center geometry.
  binary-native-selector-atom-hecke-dichotomy: that computes the Gram after two selector words and one finite character atom have been authenticated; this prevents the minimal chained-root construction from supplying such a common Pauli atom in the first place.
  same-center-whitehead-gram-is-not-native-selector-gram: that refutes a tautological full-unitary Gram with the wrong selector type; this authenticates the two coefficient products as root words but proves their three source cells cannot have commuting centers.
---

Let `R=L_(F_2)(1,2)`, put `q=s_1t_1`, and use the anchored factors

```text
a_m=s_1t_(0^m),             b_m=s_(0^m)t_1,
a_mb_m=q                                                     (m=1,2,3).
```

Consider the minimal Steinberg incidence pattern in which each anchored
factorization is one Heisenberg cell

```text
A_m=x_(alpha_m,beta_m)(a_m),
B_m=x_(beta_m,delta_m)(b_m),
C_m=[A_m,B_m]=x_(alpha_m,delta_m)(q),                 (LNS1)
```

and the native cross-product `b_(m+1)a_m` is exposed by the literal cross
commutator `[B_(m+1),A_m]`.  Steinberg typing then forces

```text
delta_(m+1)=alpha_m.                                  (LNS2)
```

Consequently the two consecutive Pauli centers are composable roots:

```text
C_(m+1)=x_(alpha_(m+1),alpha_m)(q),
C_m    =x_(alpha_m,delta_m)(q).                       (LNS3)
```

They do not commute.  If `alpha_(m+1)!=delta_m`, their commutator is
`x_(alpha_(m+1),delta_m)(q^2)=x_(alpha_(m+1),delta_m)(q)!=1`.  If the two
outer indices coincide, they are opposite roots; their elementary-matrix
images still do not commute, because the two product orders have respectively
the unequal diagonal terms `qE_(delta_m,delta_m)` and
`qE_(alpha_m,alpha_m)`.

Thus no three-cell realization of this minimal form can both

1. expose the two native coefficients `b_2a_1=s_(00)t_0` and
   `b_3a_2=s_(000)t_(00)` as the two literal cross-commutator root words, and
2. retain the pairwise commuting `q`-center packet and simultaneous reducing
   three-Pauli carrier used in `(ARC3)`.

For example, take

```text
A_1=x_47(a_1),   B_1=x_72(b_1),   C_1=x_42(q),
A_2=x_58(a_2),   B_2=x_84(b_2),   C_2=x_54(q),
A_3=x_69(a_3),   B_3=x_95(b_3),   C_3=x_65(q).        (LNS4)
```

Then

```text
[B_2,A_1]=x_87(b_2a_1)=x_87(s_(00)t_0),
[B_3,A_2]=x_98(b_3a_2)=x_98(s_(000)t_(00)),           (LNS5)
```

but `[C_2,C_1]=x_52(q)` and `[C_3,C_2]=x_64(q)` are
nonidentity.  More directly, the new center does not even preserve the old
arm cell:

```text
[C_2,A_1]=x_57(qa_1)=x_57(a_1) !=1,
[C_3,A_2]=x_68(qa_2)=x_68(a_2) !=1.                  (LNS6)
```

Therefore cutting to the negative spectral projection of `C_2` or `C_3`
does not give the common reducing Pauli carrier used by the anchored-cell
argument.  Noncommutation alone is not being used to deny every possible
common eigenvector of the nonabelian subgroup; the obstruction is
specifically to the commuting character atom and simultaneous reduction
required by that compiler.

This is a minimal-construction fence, not a refutation of the native
cross-Gram claim.  A viable true-word compiler must duplicate arms, use a
nonliteral Whitehead composite, or otherwise authenticate the selector
occurrences without asking the same single root-incidence chain to provide
both the cross-products and the commuting Pauli centers.  A disjoint Hecke
atom alone does not repair the lost simultaneous Pauli carrier.

DERIVATION
literal-native-selector-center-chain-proof
