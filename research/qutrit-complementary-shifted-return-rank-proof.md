---
rg: 2
id: qutrit-complementary-shifted-return-rank-proof
kind: route
title: Enumerate the complementary active envelope and row-reduce its cyclotomic return matrix
target: qutrit-complementary-shifted-return-rank-88
requires:
  - first-g2-mixed-return-has-a-dihedral-half-absorber
  - qutrit-two-branch-sign-polar-has-hidden-half-absorber
artifacts:
  - experiments/qutrit_complementary_shifted_return_rank.py
---

# Complementary shifted return

## 1. The returned coefficient really is q

Use the branch-one raw roots

```text
U_1=x_(c_1,c_0)(t_1),       V_1=x_(c_0,c_3)(s_1).
```

The long router begins with

```text
c_0 -> c_1 -> c_2 -> c_3,
```

so

```text
g_2^2 U_1 g_2^(-2)=x_(c_3,c_2)(t_1).
```

The three-index Steinberg relation and `s_1t_1=q` give

```text
[V_1,g_2^2 U_1 g_2^(-2)]
=x_(c_0,c_2)(q)=P_q.
```

This differs essentially from the established branch-zero return
`x_(c_0,c_2)(1-q)`.

## 2. A finite faithful active envelope

Use the same active basis as the first shifted-return calculation,

```text
(c_0,c_3,c_1,c_1',c_2,c_2').
```

Put

```text
D=F_2{1,q,a},       a=qt_0,
q^2=q, qa=a, aq=0, a^2=0.
```

The faithful matrices are

```text
k=diag(1,1,r,r),                 r=[[0,1],[1,1]],
H=I+q(E_(5,3)+E_(6,4)),
A=I+aE_(5,1),
W=I+qE_(5,2),
P_q=I+qE_(1,5).
```

Every entry lies in the eight-element ring `D`.  Breadth-first collection by
right multiplication with

```text
k,k^(-1),H,A,W,P_q
```

closes after exactly `6144` distinct matrices.  Since `k` is faithful on the
active C3 type and the displayed root matrices are their literal active
forms, this is a faithful finite envelope, not a quotient used only for an
upper bound.

## 3. Reduce to a 768 by 2048 exact cyclotomic matrix

Let

```text
B=<H,A,W> ~= C_2^3.
```

For `(sigma,tau)` let `e_B` be the unnormalized Fourier idempotent with
character values

```text
H |-> -1,       A |-> sigma,       W |-> tau.
```

Let

```text
e_k=1+omega^2 k+omega k^2,
omega^2+omega+1=0,
```

be the selected active C3 character.  Denominators do not affect rank, so the
operator to row-reduce is

```text
e_B P_q e_B e_k.                                      (QRP1)
```

The range of `e_B` has one basis vector for every right coset of `B`, hence
`6144/8=768` basis vectors.  The range of `e_k` has one basis vector for every
right coset of `<k>`, hence `6144/3=2048` basis vectors.  Expanding `(QRP1)`
has exactly `8*8*3=192` signed cyclotomic terms before collection.

Choose one representative of each right coset.  An `e_B`-range vector is
determined by its coefficient at that representative, so each column is read
off exactly from the 192 group products.  Sparse Gaussian elimination is
performed in the field

```text
Q(omega)=Q[w]/(w^2+w+1).
```

For `x=a+b omega`, inversion is exact:

```text
x^(-1)=((a-b)-b omega)/(a^2-ab+b^2).
```

The resulting ranks are

```text
rank_(+,+)=88,
rank_(-,+)=rank_(+,-)=rank_(-,-)=84.                    (QRP2)
```

The executable artifact performs the coefficient-ring collection, group
enumeration, coset construction and rational-cyclotomic elimination from
scratch and asserts all four numbers.  No modular rank is used in the
certificate.

## 4. Put back the two h characters

The full qutrit source uses two central `h` characters out of three and the
single active `k` character.  Thus `(QRP2)` gives

```text
2*88/(3*6144)=11/1152,
2*84/(3*6144)=7/768.
```

The established branch-zero shifted return has source `43/1152` in the
`(+,+)` row.  If `X_0,X_1` denote the two compressed returns, then for every
scalar combination

```text
X=lambda_0 X_0+lambda_1 X_1
```

one has

```text
ran(X^*) <= ran(X_0^*)+ran(X_1^*),
```

and hence

```text
rank supp|X|
 <=43/1152+11/1152
 =3/64
 <1/18.
```

The same inequality holds for any operator assembled from the two returns
whose source is contained in their summed initial spaces.  Thus the
complementary branch cannot repair the first dihedral half-loss. QED
