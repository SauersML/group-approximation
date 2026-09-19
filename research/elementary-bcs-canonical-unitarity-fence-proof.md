---
rg: 2
id: elementary-bcs-canonical-unitarity-fence-proof
kind: route
title: Compute the off-diagonal defect of every elementary transvection
target: elementary-bcs-canonical-unitary-compiler-fence
requires: []
artifacts:
  - research/artifacts/finite-type-corner-clifford-collapse-2026-08-21.md
---

Let `R` be a star subring of a C-star algebra `B`, fix `i!=j`, and put

```text
T_ij(a)=I+a e_ij in M_n(B).
```

Since `e_ji e_ij=e_jj`, direct multiplication gives

```text
T_ij(a)^* T_ij(a)
 =I+a e_ij+a^* e_ji+a^*a e_jj.                         (1)
```

The `(i,j)` entry on the right side of `(1)` is `a`.  Hence
`T_ij(a)^*T_ij(a)=I` forces `a=0`.  Every nontrivial canonical elementary
root matrix is therefore nonunitary.

The universal group C-star algebra is universal for **unitary**
representations.  Consequently the canonical coefficient homomorphism

```text
EL_n(R)->GL_n(B),             e_ij(a) |-> T_ij(a),
```

cannot integrate to a star homomorphism from `C^*(EL_n(R))` to `M_n(B)`:
such a star homomorphism would send every group element to a unitary, in
contradiction with `(1)` for any nonzero coefficient.

Taking polar factors does not repair this map even on one elementary root
subgroup.  For real `t`, put

```text
T(t) = [[1,t],[0,1]],
U(t) = (t^2+4)^(-1/2) [[2,t],[-t,2]],
```

where `U(t)` is the polar unitary of `T(t)`.  Although `T(1)^2=T(2)`, direct
multiplication gives `U(1)^2 != U(2)`.  Thus polar factorization already
breaks the elementary relation.  Nor can the displayed matrices themselves
be unitary compressions: for `t!=0`, `||T(t)||>1`, while every compression of
a unitary is contractive.  Scaling first and dilating individual operators
would lose the group multiplication law.  Hence neither construction turns
the coefficient representation into a unitary representation of the group.
Form-preserving elementary groups over rings with involution instead use an
indefinite algebraic form, which does not change the positive-Hilbert-space
calculation `(1)`.

An unrelated abstract unitary representation of `EL_n(R)` is logically
possible, but it no longer extends the canonical coefficient matrices.  The
primary-source scope audit in the artifact records the exact available
rigidity ranges.  Peterson--Thom, Theorem 3.6, treats
`PSL_m(BS^(-1))`, where `B` is an order, `m>=2`, and the rank-two case has
infinitely many units.  Lavi--Levit treats `EL_d(R)` for a commutative
Noetherian unital ring with `d>max(sr(R),2)`; their further-questions section
leaves noncommutative rings open.  Neither theorem applies to the
noncommutative BCS star ring.  In the Peterson--Thom range, asking for a
generating non-CE `II_1` factor representation and then applying Theorem 3.6
already identifies that factor with the regular factor, which is the final
nonhyperlinearity conclusion rather than a coefficient-ring compiler.  This
proves both the canonical obstruction and the stated boundary on the
abstract repair.
