# The column models retain the head after imposing the first actor relation

2026-09-08. The explicit finite windows from the
[whole-column construction](jacobson-whole-column-normalizer-has-marked-lef-models-2026-09-08.md)
satisfy the literal actor relation `[u,h v h]^2=1` in every
size, for the complement specified below. Thus adding this relation
does not force the marked additive element to vanish in matrix coronas.
The proof is finite linear algebra over `F_2`; it uses no infinite-group
invariant-vector estimate.

This is a statement about a particular quotient of the column cover.
Faithfulness on its actor subgroup and the MF property of that quotient
are not established. Section 5 gives a second fixed literal actor
relation whose error is exactly `2` in every window of size `n>=5`.
The quotient remains a proper cover of the literal column normalizer,
and these models do not descend to that normalizer or to the full
coherent Jacobson group.

## 1. The quotient and the assertion

Write

```text
J=F_2<S,T | TS=1>,    Q=1-ST,    N=(J,+)^2,
K=GL_2(F_2) * <h | h^2=1>,
H_col=N semidirect K.
```

Constants act on the two coordinates of `N`, and

```text
h(a,b)=F(a,b)=(Qa+Sb,Ta).
```

Let `u=x_12(1), v=x_21(1)` in the constant actor factor and put

```text
r=[u,h v h],       K_1=K/<<r^2>>,
H_1=H_col/<<r^2>>.
```

The literal two-by-two calculation in the whole-column artifact gives
`r=x_12(SQ)` on `N`. In particular `r^2` acts identically on `N`.
Its normal closure in `K` also acts identically, so the action descends
to `K_1`. Moreover the normal closure of the pure actor `r^2` in
`H_col` is the same subgroup as its normal closure in `K`: every
element of that subgroup centralizes `N`. Consequently

```text
H_1=N semidirect K_1,                                (1)
```

with `N` still embedded.

**Proposition.** There is a homomorphism from `H_1` into a norm matrix
corona that is injective on `N`. It has permutation-matrix lifts. Every
fixed nonzero element of `N` has norm distance `2` from the identity
at all sufficiently large coordinates of these lifts.

In particular `(Q,0)` survives this corona homomorphism. Nevertheless
every exact finite-dimensional unitary representation of `H_1` kills
`(JQJ)^2`, by composing with the quotient map from `H_col` and applying
the exact-representation calculation in the whole-column artifact.

## 2. The complement and its exact involution table

For `n>=2`, abbreviate

```text
x_(i,j)=(S^i T^j,0),        y_(i,j)=(0,S^i T^j),
A_n=span{x_(i,j),y_(i,j):0<=i,j<n}.
```

The normal monomials `S^i T^j` are linearly independent in `J`.
Put

```text
d_j=x_(n,j)                         (0<=j<n),
d_*=x_(0,n-1)+x_(1,n)+y_(0,n),
D_n=span{d_*,d_0,...,d_(n-1)}.
```

Their classes modulo `A_n` are independent: the `d_j` have distinct
first-coordinate monomials with first index `n`, whereas the class of
`d_*` has the unique second-coordinate monomial `y_(0,n)`. Thus

```text
W_n=A_n directSum D_n,        dim W_n=2n^2+n+1.       (2)
```

In fact `W_n=A_n+F(A_n)`. This follows from the complete table

```text
F x_(i,j) = y_(i-1,j)                           (1<=i<n),
F x_(0,j) = x_(0,j)+x_(1,j+1)+y_(0,j+1)         (j<n-1),
F x_(0,n-1) = d_*,
F y_(i,j) = x_(i+1,j)                          (0<=i<n),
F d_j = y_(n-1,j),
F d_* = x_(0,n-1).                              (3)
```

Here and below `x_(n,j)` means `d_j`. The first four lines follow
from `QS=0`, `TS=1`, and `QT^j=T^j+ST^(j+1)`. They show that
`F(A_n)<=W_n`, that every `d_j` and `d_*` lies in `F(A_n)`, and
that `A_n+F(A_n)=W_n`. The last two lines also follow directly,
or from `F^2=1`. In particular `F` is an involution of `W_n`.

Let `GL_2(F_2)` act naturally on `A_n` and trivially on `D_n`.
Together with (3), this defines an exact actor representation

```text
rho_n:K -> GL(W_n).                                 (4)
```

The complement matters here. No claim that an arbitrary complement
in the earlier construction has the relation below is needed.

## 3. The first actor relation holds in every size

Write

```text
rho_n(u)=I+X,     rho_n(v)=I+Y,     B=FYF.
```

Then `X y_(i,j)=x_(i,j)` and `Y x_(i,j)=y_(i,j)` for
`0<=i,j<n`. Both operators kill `D_n`; `X` kills the first
coordinate, and `Y` kills the second. Thus `X^2=Y^2=0`.

Applying (3) twice gives the following complete table for `B`:

```text
B x_(0,j) = x_(1,j)+x_(2,j+1)             (0<=j<n-1),
B y_(i,j) = x_(i+2,j)                    (0<=i<n-1),
B d_* = x_(1,n-1),
B = 0 on all remaining basis vectors.                (5)
```

For instance, `F x_(0,n-1)=d_*`, which `Y` kills; this accounts
for the exceptional last column in the first line. Likewise
`F y_(n-1,j)=d_j` is killed by `Y`. When `n=2`, every occurrence
of `x_(2,j)` in (5) is the vector `d_j`, so the same table applies
without omitting the smallest size.

Every value in (5) is a combination of first-coordinate basis vectors
and `d_j`. The operator `X` kills all these vectors. Therefore

```text
XB=0,               X^2=B^2=0.                     (6)
```

Here `B^2=FY^2F=0` also follows without the table. Expanding the
commutator in characteristic two, using (6), gives

```text
rho_n(r)=(I+X)(I+B)(I+X)(I+B)=I+BX,
(BX)^2=B(XB)X=0,
rho_n(r^2)=I.                                      (7)
```

Thus (4) factors through `K_1` for every `n>=2`. The models do
not kill `r` itself: `BX y_(0,0)=x_(1,0)+x_(2,1)` is nonzero
in all these sizes.

## 4. The corona homomorphism retains the whole column

Choose a linear retraction `p_n:N->W_n`. This is possible because
`W_n` is a finite-dimensional subspace of `N`. Let `tau_c` denote
translation by `c` on the finite set `W_n`. For `(a,k) in H_1`
define the permutation

```text
V_n(a,k)=tau_(p_n(a)) rho_n(k)   on W_n.             (8)
```

The actor part is a genuine homomorphism on `K_1`, by (7).
The translation part is a genuine additive homomorphism on `N`.

For a fixed actor word and a fixed vector `a in N`, its finitely
many intermediate images under the letters of the word all lie in
`A_n` for sufficiently large `n`, since the `A_n` exhaust `N`.
On `A_n`, each constant actor and `F` act exactly as their original
actions on `N`. The retraction fixes these vectors. It follows that

```text
rho_n(k)p_n(a)=p_n(k a)                             (9)
```

for every fixed pair `(k,a)` and all sufficiently large `n`.
Choosing a representative word for `k` is used only to prove (9);
the left side of (9) is independent of that choice by (7).

The semidirect product law and (9) imply that, for each fixed pair
`g_1,g_2 in H_1`,

```text
V_n(g_1)V_n(g_2)=V_n(g_1 g_2)
```

eventually. Passing from permutations to their unitary matrices on
`ell^2(W_n)` therefore gives a homomorphism

```text
H_1 -> U(product_n M_(|W_n|)(C) / directSum_norm M_(|W_n|)(C)).
```

If `0!=a in N`, then `a in A_n` and `p_n(a)=a!=0` eventually.
Its translation has order two and consists entirely of two-cycles.
The corresponding permutation unitary has norm distance `2` from
identity. This proves injectivity on all of `N`, and proves the
proposition.

The separate finite quotients of the free-product actor used to make
the earlier cover models faithful are omitted here. Those factors can
retain `r^2` and would prevent passage to `K_1`. Without them, no
faithfulness assertion on `K_1` has been established. The next section
exhibits a further literal two-row actor relation that these windows
fail. The unrestricted marked matrix gap is still open.

## 5. A second fixed literal actor relation fails in every large window

Let `w_0=u v u` be the constant coordinate swap, and put

```text
a=h w_0,             r_j=a^j r a^(-j),
c_2=[u,a^2 u a^(-2)],
p=[r_1,r_(-1)] [r_2,r_0],
e=c_2 p^(-1).                                       (10)
```

These are fixed words, independent of `n`. Since `w_0 u w_0=v`,
the earlier `r` is also `[u,a u a^(-1)]`.

First compute their literal actions using the faithful unilateral
representation of `J` on two rows. Relabel the basis as

```text
e_(1,m)=f_m,          e_(2,m)=f_(-m-1)       (m>=0).
```

Then `a f_k=f_(k+1)` on the basis indexed by all integers. Write
`E_(i,j)` for the operator taking `f_j` to `f_i` and killing the
other basis vectors. The constant shear satisfies

```text
u=I+sum_(m>=0) E_(m,-m-1).
```

Each displayed sum acts finitely on each vector. Shifting this formula
by one or two positions and multiplying gives

```text
r_j=I+E_(j+1,j-1),
c_2=I+E_(2,-2)+E_(3,-1).                            (11)
```

For the second identity, set `X_0=u-I` and
`Y_2=a^2 X_0 a^(-2)`. The source and target indices show
`X_0 Y_2=0` and `Y_2 X_0=E_(2,-2)+E_(3,-1)`; both
operators square to zero. The commutator expansion used in (7)
proves (11). The same calculation with a shift by one gives `r_0`.

Elementary matrix-unit multiplication now yields

```text
[r_1,r_(-1)]=I+E_(2,-2),
[r_2,r_0]=I+E_(3,-1).
```

Their added matrix units have zero products in both orders. Therefore
`p=c_2` and

```text
e=1 in the literal actor group.                     (12)
```

In contrast, fix `n>=5` in the windows above and abbreviate

```text
A=rho_n(a),       z=y_(n-3,0),       x=x_(n-1,0).
```

On the indicated basis vectors, (3) gives

```text
A x_(i,j)=x_(i+1,j)        (0<=i<n),
A d_j=y_(n-1,j),
A y_(i,j)=y_(i-1,j)        (1<=i<n).                (13)
```

As before `x_(n,j)=d_j`. Put `B_2=A^2 X A^(-2)`.
Tracing the steps in (13) gives

```text
B_2 z=y_(n-1,0),
B_2 y_(n-1,0)=0,
B_2 x_(n-3,0)=0,          B_2 x=0.                 (14)
```

For example `A^(-2) z=y_(n-1,0)`, which `X` sends to
`x_(n-1,0)`. Its two forward shifts are `d_0` and then
`y_(n-1,0)`. Also `A^(-2)y_(n-1,0)=x_(n-1,0)`,
which `X` kills. The inverse paths of `x_(n-3,0)` and `x`
stay in the first coordinate; the smallest first index is `n-5>=0`.
This explains every line of (14).

Applying the four factors of

```text
rho_n(c_2)=(I+X)(I+B_2)(I+X)(I+B_2)
```

from right to left, using (14), gives

```text
rho_n(c_2) z=z+x,          rho_n(c_2) x=x.           (15)
```

The correction product `p` fixes both vectors. Indeed (5)--(7) show
that `rho_n(r)-I=BX` acts only on vectors `y_(0,j)` with
`j<n-1`. For `j=-1,0,1,2`, the respective preimages `A^(-j)z`
are

```text
y_(n-4,0), y_(n-3,0), y_(n-2,0), y_(n-1,0),
```

all with positive first index. The respective `A^(-j)x` are

```text
d_0, x_(n-1,0), x_(n-2,0), x_(n-3,0).
```

All these vectors are fixed by `rho_n(r)`. Thus every `rho_n(r_j)`
used in `p`, and consequently `rho_n(p)` and its inverse, fix `z`
and `x`. Equations (10) and (15) give

```text
rho_n(e)z=z+x,          rho_n(e)x=x.                 (16)
```

Linearity makes `rho_n(e)(z+x)=z`. Since `x!=0`, this is a
two-cycle on the finite set `W_n`. The permutation unitary on
`ell^2(W_n)` has eigenvalue `-1` on
`delta_z-delta_(z+x)`, and therefore

```text
||V_n(0,e)-I||=2                    for every n>=5.   (17)
```

In particular `e` is nontrivial in `K_1`, because (4) factors through
that group. Together with (12), this proves that the new actor quotient
is still a proper cover. Its specific corona map does not descend to
the literal column normalizer. This does not rule out other models of
the normalizer, and does not prove a non-MF result for it.

## 6. Verification

Two independent written checks verified the table, including `n=2`,
the commutator expansions, the quotient corona argument, and the second
fixed relation's literal identity and exact norm-2 failure. The prior
[remote replay](nonmf-column-cairn-validation-2026-09-08.json) computed
zero defect for `rho_n(r^2)` at `n=2,3,4,5,6`. Equations (2)--(9)
are the all-size proof; the finite replay alone is not that proof.
Cairn records the dependency and status of this result, not a
kernel-checked formal derivation of its linear algebra.
