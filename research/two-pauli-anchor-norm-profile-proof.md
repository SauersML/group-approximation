---
rg: 2
id: two-pauli-anchor-norm-profile-proof
kind: route
title: Apply the classical label gap to norms of Pauli coefficients
target: two-pauli-anchors-localize-arbitrary-normalizer-twists
requires:
  - bounded-involutive-cayley-expanders-for-sl-n-two
  - pauli-generator-average-has-inverse-linear-gap
---

Expand in the orthonormal Weyl basis of the old factor:

```text
W_(v,phi)=X_v Z_phi,
T=sum_w W_w tensor T_w,
||T-E(T)||_2^2=sum_(w!=0)||T_w||_(2,r)^2.
```

Set `f(w)=||T_w||_(2,r)` for `w!=0`.  Conjugation by `C_s tensor B_s`
permutes Weyl labels by `s` and conjugates each coefficient by `B_s`.
The reverse triangle inequality, followed by orthogonality, therefore gives

```text
||f-s.f||_(ell^2(Omega))^2 <= ||[T,C_s tensor B_s]||_2^2.
```

Consequently `(TAL1)` gives `||f-Pi f||<=e/sqrt(kappa)`.  This is a gap
for the scalar norm profile; it makes no assertion that conjugation by
the unrelated `B_s` forms a group representation.

Every orbit with `v!=0` projects uniformly onto `V\{0}`.  Indeed the
projection is equivariant and `GL_n(2)` is transitive on the target, so
all its fibers on an orbit have the same size.  On these orbits select
the labels with `v_1=1`.  On the remaining orbit, where `v=0,phi!=0`,
select `phi_1=1`.  Denote the union of the selected subsets by `B`.
On each orbit its proportion is

```text
theta=2^(n-1)/(2^n-1) >= 1/2.
```

Anticommutation with the coordinate Paulis gives the exact identities

```text
||[T,Z_1 tensor I]||_2^2=4 sum_(v_1=1)||T_(v,phi)||_(2,r)^2,
||[T,X_1 tensor I]||_2^2=4 sum_(phi_1=1)||T_(v,phi)||_(2,r)^2.
```

Thus `||1_B f||<=sqrt(A)/2`.  Since `Pi f` is constant on each orbit,

```text
||Pi f|| <= sqrt(2)||1_B Pi f||
 <= sqrt(2)(||1_B f||+||f-Pi f||).
```

Adding `||f-Pi f||` proves `(TAL2)`.  Uniform bounded Cayley expansion
supplies `(TAL1)` on this particular permutation representation, regardless
of the number of orbits; only its invariant subspace is projected away.

For approximate covariance, put `Q_s=(C_s^* tensor I)D_s` and let `b_s^2`
be the coordinate sum in `(TAL3)`.  Unitary invariance identifies that sum
with `sum_j||[Q_s,P_j tensor I]||_2^2`.  The coordinate Pauli gap yields

```text
a_s^2=||Q_s-E(Q_s)||_2^2 <= b_s^2/4.
```

Write `E(Q_s)=I tensor Z_s`.  The matrix `Z_s` is a contraction.  Choose
a unitary polar extension `B_s` of `Z_s` in the same square matrix algebra
`M_r`; its action on the kernel can be filled by any isometry between the
equal-dimensional complementary spaces.  Orthogonality of conditional
expectation and `||Q_s||_2=1` imply

```text
||Q_s-I tensor B_s||_2^2
 =2-2 tr_r(|Z_s|)
 <=2-2 tr_r(|Z_s|^2)
 =2 a_s^2 <= b_s^2/2.
```

Set `D'_s=C_s tensor B_s`.  For the contraction `T`,

```text
||[T,D'_s]||_2 <= ||[T,D_s]||_2+2||D_s-D'_s||_2.
```

Taking root mean squares over `S` bounds the left side by `e+sqrt(2)b`.
Apply `(TAL2)` to the individual exact normalizers `D'_s` to obtain
`(TAL4)`.  No compatibility between their polar extensions is used, and
no enlargement of matrix dimension is needed in this step.
