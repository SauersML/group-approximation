---
rg: 2
id: two-letter-dihedral-swap-wordizes-one-gram-row
kind: claim
title: Two separate block letters wordize a Gram row through one dihedral swap
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that assumes the hybrid block involution `diag(A,B)` has already been manufactured; this uses two unrelated block-diagonal letters and proves that their uncontrolled complementary blocks only contribute extra nonnegative energy.
  dihedral-spin-packet-supplies-common-partial-swap: that extracts the common partial isometry from the D8 spin sector; this shows how a private occurrence letter and one literally shared variable letter can use that partial isometry without first being combined into one hybrid letter.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that obstructs a universally oriented nonlinear hybrid predicate word; this removes the hybrid-word requirement for consistency rows but does not manufacture the nonlinear predicate reflection.
---

**ESTABLISHED.**  Let `(M,tau)` be a finite tracial matrix algebra.  Suppose
`y,z,j,a,b` are self-adjoint unitaries such that `y` is central and

```text
zj=yjz,                 [a,y]=[a,z]=[b,y]=[b,z]=1.     (TLD1)
```

Put

```text
P=(1-y)/2,              E_+=P(1+z)/2,
E_-=P(1-z)/2,           S=E_+jE_-.                    (TLD2)
```

Thus `j` exchanges the two `z` halves of the marked spin sector and `S` is
a partial isometry from `E_-` to `E_+`.  Compress the two independently
named row letters as

```text
A=E_+aE_+,              C=E_-aE_-,
D=E_+bE_+,              B=E_-bE_-.                   (TLD3)
```

Then the one ordinary word

```text
w(a,b)=ajbj                                               (TLD4)
```

satisfies the exact square identity

```text
||(w(a,b)-1)P||_2^2
 =||AS-SB||_2^2+||CS^*-S^*D||_2^2
 >=||AS-SB||_2^2.                                    (TLD5)
```

The norms on the right are the ambient normalized Hilbert--Schmidt norms
of the corresponding rectangular corners.  In particular, a private
occurrence involution `a_(c,x)` and one literally shared variable
involution `b_x` pay the desired consistency row

```text
||A_(c,x)S-SB_x||_2^2                                (TLD6)
```

without any group word whose represented value must be
`diag(A_(c,x),B_x)`.  The other diagonal blocks of the two letters are
uncontrolled, but they occur only in the second nonnegative term of
`(TLD5)`.

## Proof

Since `P` commutes with all five letters, right multiplication by the
unitary `bj` gives

```text
(ajbj-1)P=(aj-jb)bjP,
||(ajbj-1)P||_2=||(aj-jb)P||_2.                       (TLD7)
```

On `P`, relation `(TLD1)` says that `j` anticommutes with `z`.  Relative to
`PH=E_+H direct_sum E_-H`, it therefore has the exact form

```text
jP=[[0,S],[S^*,0]],
aP=diag(A,C),             bP=diag(D,B).               (TLD8)
```

Consequently

```text
(aj-jb)P=[[0,AS-SB],[CS^*-S^*D,0]].                   (TLD9)
```

The two rectangular blocks have orthogonal sources and ranges.  Taking the
tracial Hilbert--Schmidt square in `(TLD7)--(TLD9)` proves `(TLD5)`.

## Exact tracial completeness

This asymmetric syntax preserves the standard-form perfect model.  On
`H direct_sum bar(H)` use the common modular swap of
`perfect-tracial-bcs-has-one-common-module-swap` and set

```text
a_(c,x)=diag(L_(A_(c,x)),I),
b_x    =diag(I,overline(R_(B_x))).                    (TLD10)
```

The opposite blocks in `(TLD5)` are both identities, while standard-form
duality gives `L_(A_(c,x))S=S overline(R_(B_x))`.
Hence every word `a_(c,x) j b_x j` is exactly `1`.  Within-context
commutation of the private `a_(c,x)` and the involution laws also hold.
No relation between observables belonging to different contexts is added.

For approximate finite models, exactify the fixed D8 table and round the
letters commuting with `y,z` by the four spectral corners.  Conditional
expectation onto those corners and polar rounding have a
dimension-independent modulus controlled by the involution and commutator
defects.  Applying `(TLD5)` to the rounded letters therefore gives `(TLD6)`
up to `o(1)` from a fixed finite relator menu.

## Precise gain and remaining boundary

The common-swap compiler no longer needs to authenticate the consistency
hybrid `diag(A_(c,x),B_x)`: literal sharing of `b_x` already shares the
variable-player block across every incident context, while every context
keeps its private upper letter.

This does **not** authenticate a nonlinear predicate.  Taking `b=1` would
wordize `(H_c-I)S` once a private upper-block reflection
`H_c=I-2F_c` had been supplied, but tying that letter to the Boolean context
observables on the whole marked source is exactly the selector-induction /
selected-carrier problem.  Thus `(TLD5)` deletes the hybrid consistency
assembly from the terminal, but it neither proves the promotion inequality
`(CPS9)` nor evades `finite-role-packet-cannot-supply-hybrid-predicate-row`.

