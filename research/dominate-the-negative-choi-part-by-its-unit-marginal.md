---
rg: 2
id: dominate-the-negative-choi-part-by-its-unit-marginal
kind: route
title: Dominate the negative Choi part by a finite matrix marginal that vanishes on unital-zero maps
target: tree-face-separator-signedness-is-removable-modulo-the-unit
requires:
  - three-face-quotient-separators-are-not-one-face-local
---

Write

```text
B=direct_sum_(r=1)^s M_(n_r).
```

The Choi transform is a bounded linear isomorphism

```text
C:L(B,Q) -> direct_sum_r M_(n_r)(Q),
C(theta)_r=[theta(e_ij^r)]_(i,j).                              (1)
```

It preserves adjoints, and Choi's theorem says that `theta` is completely
positive exactly when every block of `C(theta)` is positive.  Hence `F`
corresponds to a bounded Hermitian functional `omega` on the C-star algebra

```text
D=direct_sum_r M_(n_r)(Q).
```

Take its Jordan decomposition

```text
omega=omega_+-omega_-.
```

For each summand let `omega_-,r` be the restriction of `omega_-` and define
its positive unit marginal

```text
lambda_r(q)=omega_-,r(I_(n_r) tensor q),       q in Q.
```

Put `lambda=sum_r lambda_r` and `N=max_r n_r`.  Define the positive
functional on `D`

```text
Lambda([X_r])=lambda(sum_(r,i) (X_r)_(ii)).                    (2)
```

We claim

```text
omega_- <= N Lambda.                                          (3)
```

It is enough to prove the one-block estimate.  Represent a positive
functional `nu` on `M_n(Q)` by a cyclic vector in a representation, identify
that representation with the amplification of a representation `pi` of
`Q`, and write the vector as

```text
xi=sum_i e_i tensor xi_i.
```

For `X=[x_ij]>=0`, positivity of each two-by-two compression and
Cauchy--Schwarz give

```text
|<pi(x_ij)xi_j,xi_i>| <= sqrt(a_i a_j),
a_i=<pi(x_ii)xi_i,xi_i>.
```

Therefore

```text
nu(X) <= (sum_i sqrt(a_i))^2
       <= n sum_i a_i
       <= n sum_i lambda_nu(x_ii),                            (4)
```

where `lambda_nu(q)=nu(I_n tensor q)`.  Applying `(4)` to every summand,
using `n_r<=N` and `lambda_r<=lambda`, proves `(3)`.

Now set

```text
omega_pos=omega+N Lambda
         =omega_+ +(N Lambda-omega_-).                        (5)
```

Equation `(3)` makes `omega_pos` positive.  If `psi(1_B)=0`, then the sum of
the diagonal Choi entries is zero, so

```text
Lambda(C(psi))=lambda(psi(1_B))=0.
```

Thus the functional `F_pos` represented by `omega_pos` satisfies `(PCU1)`
and `(PCU2)`.

For the norm estimate, if `d_B=sum_r n_r`, then

```text
||Lambda||=Lambda(1_D)=d_B ||lambda||
                         =d_B ||omega_-||.
```

Consequently

```text
||omega_pos|| <= ||omega_+||+N d_B ||omega_-||
              <= max(1,N d_B)||omega||.                       (6)
```

Combining `(6)` with the fixed norms of the Choi isomorphism and its inverse
gives `(PCU3)`.

Finally take the quantitative tree component from `(SQS10)`.  Its defect is
unital-zero, so `(PCU2)` preserves the lower bound `delta/2`.  The component
norm is bounded above by the norm of the normalized separator times the
fixed precomposition map coming from `R_H`; `(PCU3)` therefore gives the
fixed normalized lower bound `(PCU5)`.  The GNS theorem applied to the
positive functional `omega_pos` gives `(PCU6)`.  Nothing in this argument
forces that GNS representation to be finite-dimensional or to factor
through any prescribed packet, which proves the scope statement.
