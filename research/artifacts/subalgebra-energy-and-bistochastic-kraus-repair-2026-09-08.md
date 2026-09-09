# Exact subalgebra repair for bistochastic channels

2026-09-08. Written finite-dimensional proof, using normalized trace
`tr=Tr/d`. No local code, build, numerical search or new Lean
verification. All algebras and their representation multiplicities
below are arbitrary.

## 1. Statement

Let `P:M_d->M_d` be UCP, trace-preserving and self-adjoint on
`L^2(M_d,tr)`. Let `B subset M_d` be a unital subalgebra. Define

```text
a=a_B(P)=integral_(u in U(B)) [1-Re tr(u*P(u))] du.     (1)
```

The Haar measure is normalized. The integrand is nonnegative by
`L^2` contractivity. There is a self-adjoint bistochastic UCP map
`Q` satisfying

```text
Q(b_1 x b_2)=b_1 Q(x) b_2,
Q(b)=b,                 b,b_1,b_2 in B,
||P-Q||_(infinity->2)<=2 sqrt(2a).                    (2)
```

For example, `sup_(u in U(B))||P(u)-u||_2<=epsilon` implies
`a<=epsilon`. Near idempotence of `P` is not a hypothesis and
does not by itself supply a suitable `B` satisfying a small bound.

## 2. Project the Kraus operators

Write

```text
P(x)=sum_k v_k* x v_k,
sum_k v_k* v_k=sum_k v_k v_k*=I,
d_k=E_(B')(v_k).
```

Since averaging conjugation by `U(B)` is `E_(B')`,

```text
sum_k ||v_k-d_k||_2^2=a.                             (3)
```

Indeed, `sum_k ||u v_k-v_k u||_2^2` equals
`2-2Re tr(u*P(u))`; integration and the orthogonal-projection
identity give (3).

Set

```text
H=I-sum_k d_k* d_k,       G=I-sum_k d_k d_k*.
```

Schwarz for `E_(B')` gives `H,G>=0`, and both belong to `B'`.
Equation (3) and trace preservation give

```text
tr(H)=tr(G)=a.                                       (4)
```

The two deficits need not be equal. This is the extra issue when
the commutant is noncommutative. They nevertheless have equal trace
on each central summand of `B'`: all the `d_k` are block diagonal,
and on any one summand the traces of `d_k*d_k` and `d_k d_k*`
agree separately.

## 3. Balance both marginals inside the commutant

Represent

```text
B'=direct_sum_i (I_(a_i) tensor M_(b_i)).
```

On one simple multiplicity factor, diagonalize the two deficits as

```text
H_i=sum_alpha h_alpha |h_alpha><h_alpha|,
G_i=sum_beta  g_beta  |g_beta ><g_beta |,
t_i=Tr(H_i)=Tr(G_i).
```

For `t_i>0`, the operators

```text
w_(beta,alpha)=sqrt(h_alpha g_beta/t_i)
                         |g_beta><h_alpha|
```

satisfy

```text
sum_(beta,alpha) w_(beta,alpha)*w_(beta,alpha)=H_i,
sum_(beta,alpha) w_(beta,alpha)w_(beta,alpha)*=G_i.
```

Tensor each with `I_(a_i)` and extend it by zero to other
central summands. If `t_i=0`, both positive deficits are zero
on that summand and require no operators. This gives a finite
family `w_j in B'` with exactly the full marginals `H,G`.

Define

```text
Q_0(x)=sum_k d_k* x d_k+sum_j w_j* x w_j.             (5)
```

Both marginal sums are `I`. Thus `Q_0` is UCP and trace-preserving.
Every Kraus operator commutes with `B`, so `Q_0` is `B`-bimodular
and fixes `B` pointwise.

## 4. Estimate the map and its adjoint separately

Use Stinespring columns `V=(v_k,0_j)` and `W=(d_k,w_j)`.
They are isometries. Normalize their rectangular HS norm by the
common domain dimension `d`, not the larger dilation dimension.
Equations (3)--(4) give

```text
||V-W||_2^2=sum_k||v_k-d_k||_2^2+sum_j||w_j||_2^2
           =2a.
```

For a contraction `x`, expanding
`V*(I tensor x)V-W*(I tensor x)W` yields

```text
||P-Q_0||_(infinity->2)<=2 sqrt(2a).                 (6)
```

One cannot obtain the same mixed-norm bound for adjoints merely
by taking adjoints of maps. Instead use the Kraus lists
`v_k*`, `d_k*`, `w_j*`. Both new columns are again isometries
because the original maps preserve trace. The sum of squared
differences is still `2a`. Applying the same proof gives

```text
||P*-Q_0*||_(infinity->2)<=2 sqrt(2a).
```

Here `*` on maps denotes their Hilbert-space adjoint. Since
`P*=P`, the map `Q=(Q_0+Q_0*)/2` has all the properties in (2).
The adjoint Kraus operators also lie in `B'`, so averaging
preserves exact bimodularity and fixation.

## 5. A supplied approximate range yields an expectation estimate

Every map `R` fixing `B` pointwise obeys

```text
a_B(P)<=||P-R||_(infinity->2),                        (7)
```

by applying trace Cauchy--Schwarz to `u*(u-P(u))` in (1).
This gives a necessary condition as well as the sufficient bound
in (2).

Put `E=E_B`, `gamma=2 sqrt(2a)`, and
`beta=||(I-E)P||_(infinity->2)`. The repaired channel satisfies
`EQ=E`: this follows either from self-adjointness and `QE=E`,
or from trace preservation and bimodularity. Since `I-E` is
an `L^2` contraction,

```text
||Q-E||_(infinity->2)=||(I-E)Q||_(infinity->2)
 <=gamma+beta.
```

Therefore

```text
||P-E_B||_(infinity->2)<=beta+4 sqrt(2a_B(P)).          (8)
```

The algebra in (8) is supplied in advance. The statement does not
extract it from the approximate image of a channel.

## 6. The square-root scale is already necessary in dimension two

Let `D` be the diagonal algebra in `M_2`, set

```text
Z=diag(1,-1),       X=[0 1;1 0],
J_theta=cos(theta) Z+sin(theta) X,
P_theta(x)=(x+J_theta x J_theta)/2.
```

The matrix `J_theta` is a self-adjoint involution. The map
`P_theta` is the exact expectation onto `span{I,J_theta}`;
it is bistochastic, self-adjoint and positive on `L^2`.
Direct computation gives

```text
P_theta(Z)=cos(theta)J_theta,
||P_theta(Z)-Z||_2=|sin(theta)|,
a_D(P_theta)=(1/2)sin(theta)^2.                      (9)
```

For the last identity write a diagonal unitary as `alpha I+beta Z`.
Its two phases are independent under Haar measure, so
`integral |beta|^2=1/2`; only the `Z` component contributes to
(1). Every channel fixing `D` fixes `Z`, and hence has distance
from `P_theta` at least

```text
sqrt(2a_D(P_theta)).
```

As `theta->0`, this excludes a uniform linear bound in the
averaged energy, even for exact expectations in fixed dimension.

The result permits arbitrary noncommutative `B` and represented
multiplicities. Its remaining limitation is the requirement to
identify `B`. It proves neither general near-idempotent rounding
nor the nonhyperlinear-group goal.
