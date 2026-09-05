# Rank integrality and compressed irreducible representations

The uniform theorem `(QRC5)` passes the compressed-representation test.
Below the Frobenius defect threshold, integrality makes the exceptional
projection zero and a same-dimensional iteration converges. Above that
threshold, compressions of large irreducible Kazhdan representations
show why dimension flexibility is indispensable and why a universal
padding bound smaller than the squared normalized-HS defect is impossible.

## 1. A regime where the QRC iteration closes

Fix epsilon equal to one in `(QRC5)`, and let `A,C,delta_0>0` be its
uniform constants. In dimension `d`, suppose

```text
0<delta<delta_0,       C d delta^2<1.                   (CRI1)
```

The exceptional projection has rank at most `C d delta^2<1`, hence
is zero. Its two complementary norms now sum to twice the full relator
norm. Thus the new tuple has defect at most `delta/2` and generator
displacement at most `A delta`.

Apply the same constants again. The defect decreases, so `(CRI1)`
continues to hold. If an exact tuple occurs, stop. Otherwise the
iterated generator displacements sum to at most `2A delta`. In the
fixed matrix dimension this gives a convergent unitary tuple. Continuity
of the defining words makes its limit an exact representation. Therefore

```text
dist_2(U,Rep_d(G))<=2A delta.                           (CRI2)
```

This infinite iteration is valid because the same finite-scale constants
apply at every step and no support surgery is needed.

Writing `delta_F=sqrt(d)delta` gives a uniform Frobenius statement:
if `delta_F<min(delta_0,C^(-1/2))`, exact correction in the original
dimension has generator Frobenius distance at most `2A delta_F`.
This does not extend the radius to a fixed normalized-HS neighborhood
independently of dimension.

## 2. Polar compression loses only k directions per generator

Let `G` have a finite symmetric Kazhdan generating set `S` with constant
`kappa` in the convention
`dist(v,H^G)<=kappa^(-1)max_s||pi(s)v-v||`. Let
`rho:G->U(N)` be irreducible. Remove a `k`-dimensional subspace, put
`d=N-k`, and let `W:C^d->C^N` include the remaining space. Set

```text
B_s=W^*rho(s)W.
```

Extend each square contraction's polar part to a unitary `U_s`, with
consistent choices for inverse letters. Since

```text
I-B_s^*B_s=W^*rho(s)^*(I-WW^*)rho(s)W
```

has rank at most `k`, at least `d-k` singular values of `B_s` equal
one. On their right singular subspace `rho(s)W` equals `WU_s` and
has no component in the removed space. Thus

```text
R_s=rho(s)W-WU_s,
rank(R_s)<=k,
||R_s||_HS^2=2 sum_i(1-c_i)<=2k,                       (CRI3)
```

where `c_i` are the singular values of `B_s`. For a fixed presentation
on `S` with maximal relator length `ell`, telescoping gives

```text
rank(U(r)-I)<=|r|k,
||U(r)-I||_HS<=|r|sqrt(2k),
delta^2 d<=2 ell^2 k.                                 (CRI4)
```

Consequently deleting `k=o(N)` dimensions gives normalized-HS
approximate representations. The relator residuals already have exact
common support of rank at most `k sum_r |r|`: take the join of their
support projections. Each residual is normal, so this works on both sides.

## 3. Close exact correction requires recovering all lost dimensions

Let `d<=D<N`, and compare `U_s direct_sum I_(D-d)` with a genuine
representation `sigma:G->U(D)`. Extend `W` to an isometry
`J:C^D->C^N` by including any additional `D-d` dimensions from the
removed space. On the original columns use `(CRI3)`; on each additional
column the difference between `rho(s)` and the identity has norm at
most two. Hence

```text
||rho(s)J-J(U_s direct_sum I)||_HS^2
 <=2k+4(D-d)<=6k.                                    (CRI5)
```

The exact unitary representation on `Hom(C^D,C^N)` defined by
`X |-> rho(g)X sigma(g)^*` has no invariant vector. A nonzero
intertwiner would have nonzero invariant range in the irreducible
`rho`, hence would be surjective, impossible when `D<N`.

Apply the Kazhdan inequality to `J`, of HS norm `sqrt(D)`. If
`e=max_s||sigma(s)-(U_s direct_sum I)||_(2,D)`, then

```text
kappa sqrt(D)<=sqrt(2k+4(D-d))+e sqrt(D),
e>=kappa-sqrt((2k+4(D-d))/D)
 >=kappa-sqrt(6k/d).                                  (CRI6)
```

This holds for every unitary identification used in the comparison.
When `k=o(N)`, the right side tends to `kappa` uniformly for
`d<=D<N`. Therefore any exact padded correction whose error tends to
zero must have `D>=N`: at least `k` dimensions must be added.

Adding them is sufficient. Comparing the supplied exact `rho` with
`U_s direct_sum I_k` gives

```text
max_s||rho(s)-(U_s direct_sum I_k)||_(2,N)
 <=sqrt(6k/N)->0.                                    (CRI7)
```

These are genuine flexible corrections, but close corrections cannot
use fewer than the removed dimensions. Combining the necessary padding
with `(CRI4)` yields

```text
(D-d)/d>=k/d>=delta^2/(2 ell^2).                       (CRI8)
```

Thus relative padding `o(delta^2)` cannot be promised uniformly.
For general growing `k`, this does not assert that `delta^2 d` is
comparable to `k`: `(CRI4)` is only an upper bound on the defect.

## 4. Deleting one dimension gives a sharp quadratic scale

Set `k=1` and let irreducible dimensions `N` tend to infinity. For
`d=N-1`, the stronger same-dimensional version of `(CRI6)` is

```text
dist_2(U,Rep_d(G))>=kappa-sqrt(2/d).                    (CRI9)
```

If the group also has all-unitary `H^2` vanishing, use the constants
from Section 1. The input defect tends to zero by `(CRI4)`. Eventually

```text
C d delta^2>=1.                                      (CRI10)
```

Otherwise `(CRI2)` would give exact same-dimensional representations
at distance at most `2A delta->0`, contradicting `(CRI9)`. Therefore

```text
1/C<=d delta^2<=2 ell^2.
```

The necessary one-dimensional padding has relative size `1/d`
comparable to `delta^2`. This lower defect bound explicitly uses
`(QRC5)` and rank integrality; it does not follow from compression alone.

## 5. The all-H2 arithmetic test

There are arbitrarily large irreducible finite-dimensional unitary
representations of `SL_5(Z)` directly from its finite quotients.
For a prime `p`, reduction maps onto `SL_5(F_p)`, by elementary
matrix generation. This group is doubly transitive on lines in
`F_p^5`: send two independent representatives to any desired pair
and adjust the determinant on a complementary direction.

Its permutation representation has commutant dimension two, the number
of orbits on ordered pairs. The constants occur once, so the orthogonal
complement is irreducible. Its dimension is

```text
(p^5-1)/(p-1)-1=p^4+p^3+p^2+p,
```

which is unbounded. This supplies the representations above without
enumerating dimensions or running computations.

The all-unitary `H^2` input for this group follows from
[Bader--Sauer, Theorems A and C and equation (1)](https://arxiv.org/html/2308.06517v3),
as audited in the arithmetic artifact. Property (T) provides a fixed
Kazhdan constant. Thus this test lies within the intended all-H2 setting.

The conclusion is that quadratic-rank normal form is consistent with a
necessary quadratic padding cost. Compressed irreducibles sometimes
require reconstruction of every deleted representation direction.
Their exact dilation is available because the original `rho` is
supplied; no such ambient representation has been constructed for an
arbitrary input tuple.

No code, build, numerical computation, or proof-kernel verification
was run for this artifact.
