---
rg: 2
id: kt-truncated-cone-inverse-rank-and-pointed-wall-proof
kind: proof
title: Rank calculation for the truncated cone inverse and the pointed return
proves:
  - kt-nilpotent-inverse-is-hs-cheap-only-before-canonical-amplification
requires:
  - kt-single-laurent-return-has-profinite-coset-models
---

# Rank calculation for the truncated cone inverse and the pointed return

## 1. The quotient basis

Put

~~~text
S=F_2[x_1,y,x_3],
P=F_2[x_1,x_1y,x_3],
T_N=S/(x_1,y,x_3)^(N+1),
P_N=image(P),
V_N=T_N/P_N.
~~~

The subspace `P_N` is spanned by the residue monomials
`x_1^a y^b x_3^c` with `a+b+c<=N` and `a>=b`. Therefore the complementary
monomial basis of `V_N` is

~~~text
B_N={x_1^a y^b x_3^c : a+b+c<=N and a<b}.                 (1)
~~~

Although `P_N` is not an ideal, multiplication by `x_1` preserves it.
Hence multiplication by `x_1` induces a well-defined linear map

~~~text
X_N:V_N->V_N.                                             (2)
~~~

## 2. Exact dimension

The number of all monomials in three variables of total degree at most
`N` is `binom(N+3,3)`. Interchanging `a` and `b` pairs the monomials with
`a<b` and `a>b`. The unpaired diagonal count is

~~~text
d_(2m)=sum_(j=0)^m (2j+1)=(m+1)^2,
d_(2m+1)=sum_(j=0)^m 2(j+1)=(m+1)(m+2).                  (3)
~~~

Consequently

~~~text
v_N=|B_N|=(binom(N+3,3)-d_N)/2,                           (4)

v_(2m)=m(m+1)(4m+5)/6,
v_(2m+1)=(m+1)(m+2)(4m+3)/6.                             (5)
~~~

These formulas give `v_N=N^3/12+O(N^2)`.

## 3. Kernel and cokernel

On the basis (1), `X_N` does exactly one of three things:

1. if `a+b+c=N`, it sends the monomial past the truncation and hence to
   zero;
2. if `a=b-1`, it sends the monomial into `P_N` and hence to zero in
   `V_N`;
3. otherwise it sends it injectively to the basis monomial
   `x_1^(a+1)y^b x_3^c`.

The cokernel has the especially simple basis consisting of the monomials
with `a=0`, `b>=1`, and `b+c<=N`. Thus

~~~text
k_N=dim coker(X_N)
   =sum_(b=1)^N (N-b+1)
   =N(N+1)/2.                                             (6)
~~~

Since `X_N` is a square linear map, its kernel has the same dimension.
This also follows directly from the first two cases above after removing
their overlap.

With the basis (1) declared orthonormal over `C`, the matrix `X_N` is a
partial permutation: it is an isometry from `ker(X_N)^perp` onto
`ran(X_N)` and is zero on its kernel.

## 4. Optimal coefficient-HS inverse

Let normalized Hilbert--Schmidt norm on `M_(v_N)(C)` be denoted by
`||.||_2`. For any matrix `Y`, the restriction of `YX_N-I` to
`ker(X_N)` is `-I`. Hence

~~~text
||YX_N-I||_2^2 >= k_N/v_N.                               (7)
~~~

For an orthonormal basis vector in `ran(X_N)^perp`, the component of
`(X_NY-I)xi` orthogonal to `ran(X_N)` is `-xi`. Therefore

~~~text
||X_NY-I||_2^2 >= k_N/v_N.                               (8)
~~~

Taking `Y=X_N^*` makes the two products the orthogonal projections onto
`ker(X_N)^perp` and `ran(X_N)`, so equality holds in both (7) and (8).
Because the kernel and cokernel have equal dimension, one may instead
extend `X_N^*:ran(X_N)->ker(X_N)^perp` by any unitary from
`ran(X_N)^perp` onto `ker(X_N)`. This gives a unitary `Y` attaining the
same two errors.

The same completion in the other direction gives a unitary `U_N` equal to
`X_N` on `ker(X_N)^perp`. Thus

~~~text
inf_(U unitary)||X_N-U||_2=sqrt(k_N/v_N).                 (9)
~~~

The lower bound in (9) follows by testing every vector in the kernel.

Substitution of (5) and (6) gives the exact squared ratios

~~~text
k_(2m)/v_(2m)=6(2m+1)/((m+1)(4m+5)),
k_(2m+1)/v_(2m+1)=6(2m+1)/((m+2)(4m+3)).                 (10)
~~~

In both cases

~~~text
k_N/v_N=6/N+O(1/N^2).                                    (11)
~~~

This proves the coefficient-carrier formula.

## 5. The named vector carries the whole obstruction

Let `eta_N` be the unit basis vector represented by `y`. It is present for
every `N>=1`, and

~~~text
X_N eta_N=[x_1y]=[x_2]=0 in V_N.                          (12)
~~~

Therefore, for every candidate inverse `Y`,

~~~text
(YX_N-I)eta_N=-eta_N,
||(YX_N-I)eta_N||=1.                                     (13)
~~~

The normalized error in (11) tends to zero only because (13), together
with the other boundary failures, is averaged over `v_N` monomial
coordinates.

Now take the exact regular wreath model from
`kt-single-laurent-return-has-profinite-coset-models` and tensor its Hilbert
space with `C^(v_N)`. Put the half projection and the named return on the
first factor, and put `X_N,Y` on the second. Tensor-product normalization
preserves both calculations:

~~~text
||[p_N tensor I,U_h,N tensor I]||_2=1/sqrt(2),

||(I tensor Y)(I tensor X_N)-I||_2
 =||(I tensor X_N)(I tensor Y)-I||_2
 =sqrt(k_N/v_N).                                         (14)
~~~

Equation (14) is the tempting absorber. It is deliberately only a
decoupled matrix row: it contains no covariance relation saying that the
inverse operator acts on the root coordinate represented by `eta_N`.
Equation (13) says exactly where that missing cross-relation fails.

## 6. Exponential rank amplification on the canonical root carrier

Let `A_N=(V_N,+)`. As a finite set it has

~~~text
|A_N|=2^(v_N),
|ker X_N|=2^(k_N),
|ran X_N|=2^(v_N-k_N).                                   (15)
~~~

For any function `Y:A_N->A_N`, the equality

~~~text
Y(X_N(a))=a
~~~

can hold for at most one member of each fiber of `X_N`. Hence

~~~text
|Fix(YX_N)| <= |ran X_N|.                                (16)
~~~

The equality `X_N(Y(a))=a` can hold only when `a in ran X_N`, giving

~~~text
|Fix(X_NY)| <= |ran X_N|.                                (17)
~~~

Both bounds are simultaneously sharp. Choose a section
`s:ran X_N->A_N`, define `Y=s` on `ran X_N`, and extend this injection to
a bijection of `A_N`. Then `X_NY` fixes `ran X_N`, while `YX_N` fixes
exactly the chosen transversal `s(ran X_N)`. Dividing (16)--(17) by
`|A_N|` gives the agreement fraction

~~~text
2^(-k_N).                                                 (18)
~~~

Thus, for the normalized counting `L^2` defect
`d_2(f,g)=sqrt(|{a:f(a)!=g(a)}|/|A_N|)`, the optimal two-sided inverse
error is

~~~text
sqrt(1-2^(-k_N)).                                         (19)
~~~

Since `k_N=N(N+1)/2`, this tends to one superpolynomially fast.

The same statement has a basis-free Hilbert-space formulation. Define
`C_X:ell^2(A_N)->ell^2(A_N)` by

~~~text
C_X delta_a=delta_(X_N(a)).                               (20)
~~~

Its rank is `|ran X_N|`. For every matrix `B`, both `BC_X` and `C_XB`
have rank at most this number. The distance in normalized HS norm from
the identity to any matrix of rank at most `r` is at least
`sqrt(1-r/|A_N|)`. The Moore--Penrose inverse makes the two products the
rank-`|ran X_N|` support projections, so

~~~text
inf_B max{||BC_X-I||_2,||C_XB-I||_2}
 =sqrt(1-2^(-k_N)).                                       (21)
~~~

This is the relevant rank scale once the additive root group, its Fourier
basis, or a canonical coset/lamp carrier is retained.

## 7. Consequence for the Laurent seam

The monomial-index completion (14) demonstrates that a scalar normalized-HS
inverse row can be made cheap without disturbing the `1/sqrt(2)` wall. It
does not extend the coherent actor. The cross-relation defining the named
return asks the inverse to act on `[y]`, where (13) has norm one; imposing
the entire finite additive root packet amplifies the defect to (19).

Therefore the nilpotent truncations do not produce a canonical approximate
representation of the first Laurent inverse direction. Any argument that
uses (11) must also explain how it controls the named boundary vector;
averaged rank alone cannot do so. Conversely, (19) is a terminal obstruction
only for this truncation and its canonical root amplification, not for an
arbitrary noncongruence unitary microstate with a moving word window. The
global non-hyperlinearity root remains open.
