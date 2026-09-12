---
rg: 2
id: first-g2-mixed-return-dihedral-half-absorber-proof
kind: route
title: Collect the ST return, expose its D8 sign, and row-reduce the finite active envelope
target: first-g2-mixed-return-has-a-dihedral-half-absorber
requires:
  - g2-one-raw-letter-sign-atlas-is-residually-finite
  - jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
  - qutrit-two-scalar-routers-leave-head-packet-finite
---

## 1. The first opposite-product return

The long actor begins with the directed cycle segment

```text
c_0 -> c_1 -> c_2 -> c_3.
```

Consequently scalar conjugation gives

```text
g_2^2 x_(c_1,c_0)(T) g_2^(-2)=x_(c_3,c_2)(T).
```

The three-index Steinberg relation now gives

```text
[V,g_2^2Ug_2^(-2)]
 =[x_(c_0,c_3)(S),x_(c_3,c_2)(T)]
 =x_(c_0,c_2)(ST)=P.                                  (GMR7)
```

For comparison, the unshifted composable chain gives

```text
[U,V]=x_(c_1,c_3)(TS)=x_(c_1,c_3)(1).                 (GMR8)
```

The one-step forward conjugate of `U` is not composable with `V`.
Thus, among the forward placements `U,g_2Ug_2^(-1),g_2^2Ug_2^(-2)`,
equations `(GMR7)--(GMR8)` are the first two-letter returns, and
`(GMR7)` is the first one which distinguishes `ST` from `TS`.

Put

```text
q=1-ST,             p=ST=1-q,             a=qT.
```

Inside the Jacobson algebra,

```text
q^2=q,       qa=a,       aq=0,       a^2=0,
pq=qp=0,    pa=0,        ap=a.                         (GMR9)
```

The three elements `1,q,a` are linearly independent in the faithful
half-line model: they are respectively the identity, `E_(0,0)`, and
`E_(0,1)`. Hence

```text
D=F_2 1 direct-sum F_2 q direct-sum F_2 a
```

is an eight-element coefficient algebra.

## 2. The hidden D8 sign

On the ordered two-coordinate corner `(c_0,c_2)` the two opposite roots
are

```text
P=[[1,p],[0,1]],                 A=[[1,0],[a,1]].
```

Using `(GMR9)`,

```text
PA=[[1,p],[a,1]],

(PA)^2=[[1,0],[0,1+a]]
      =I+aE_(c_2,c_2)=Z.                               (GMR10)
```

Both `P` and `A` are involutions, `Z` is a nonidentity involution, and
`Z` commutes with them. Therefore `PA` has order four and
`<P,A> isomorphic to D_8`.

The roots `H=x_(c_2,c_1)(q)` and `W=x_(c_2,c_3)(q)`
commute with `P` because `pq=0`. They also commute with `Z` because
`aq=0`. The already established sign roots `H,A,W` commute pairwise.
Thus

```text
B=<H,A,W,Z> isomorphic to C_2^4.                         (GMR11)
```

Let `f_sigma=(1+sigma A)/2` in the complex group algebra. From
`PAP=AZ` one obtains

```text
(f_sigma P f_sigma)^2
 =f_sigma (P f_sigma P) f_sigma
 =f_sigma(1+sigma AZ)f_sigma/2
 =f_sigma(1+Z)/2.                                      (GMR12)
```

The other defining factors of `G_(sigma,tau)` commute with
`P,A,Z`. Multiplying `(GMR12)` by those factors proves

```text
X_(sigma,tau)^2=K_(sigma,tau),

X_(sigma,tau)=G_(sigma,tau)PG_(sigma,tau),
K_(sigma,tau)=G_(sigma,tau)(1+Z)/2.                    (GMR13)
```

Here `X_(sigma,tau)` is self-adjoint and `K_(sigma,tau)` is a
projection. Hence `K_(sigma,tau)` is exactly the support of
`abs(X_(sigma,tau))`. For the qutrit cut `R`,

```text
(X_(sigma,tau)R)^*(X_(sigma,tau)R)
 =R K_(sigma,tau) R,                                   (GMR14)
```

so the polar source rank is the rank of `K_(sigma,tau)R`.

## 3. A faithful finite active matrix model

Recall the decomposition used in the original two-sign count:

```text
C=<h> times <k>,                |h|=|k|=3.
```

The line `<h>` is the kernel of the active nontrivial `C`-type, while
`k` acts through the irreducible two-dimensional `F_2[C_3]` module.
Choose its matrix

```text
r=[[0,1],[1,1]].
```

Use the ordered active basis

```text
(c_0,c_3,c_1,c_1',c_2,c_2').
```

Over `D` the active factor `F_act=<k,H,A,W,P>` has the faithful
six-dimensional matrices

```text
k=diag(1,1,r,r),

H=I+q(E_(5,3)+E_(6,4)),
A=I+aE_(5,1),
W=I+qE_(5,2),
P=I+pE_(1,5).                                          (GMR15)
```

The first two coordinates are trivial `C`-types and each primed pair is
one copy of the active irreducible type. The matrix for `H` is the
intertwining identity between the two corresponding copies. The
restrictions of `A,W,P` are the indicated vector, covector, and reverse
vector roots. Thus `(GMR15)` is the simultaneous `C`-basis form of the
actual generators, not a quotient model. The element `k` is already
faithful on this block; the remaining central factor `h` is kept
separately.

For completeness, the group order can be checked without any
floating-point calculation. Encode an element of `D` by its coefficient
triple in the basis `(1,q,a)` and multiply triples using `(GMR9)`.
Starting with `L_0={I}`, set

```text
L_(n+1)=L_n union L_n {k,k^(-1),H,A,W,P}.
```

The numbers of new canonical six-by-six matrices at distances
`0,1,...,14` are

```text
1, 6, 21, 60, 143, 292, 557, 952, 1350, 1438,
929, 308, 68, 16, 3.
```

Right multiplication of the resulting set by every displayed generator
adds no matrix. Hence

```text
|F_act|=6144.                                           (GMR16)
```

The central element `h` has trivial intersection with this active
factor, so

```text
F=<C,H,A,W,P>=<h> times F_act,             |F|=18432.   (GMR17)
```

This also gives a direct finite-envelope proof: every matrix entry lies
in the eight-element algebra `D`.

## 4. Exact qutrit-cut ranks

It remains to compute the rank in `(GMR14)`. This is a small
coset-incidence calculation, not a numerical singular-value estimate.
Let `omega^2+omega+1=0`. The two atoms in `R=e_0+e_1` choose two
different `h` characters and the same `k` character, exactly as in the
original sign-rank proof. For one fixed `h` character form, in
`C[F_act]`,

```text
b_(sigma,tau)
 =(1-H)(1+sigma A)(1+tau W)(1+Z)/16
  * (1+omega^2 k+omega k^2)/3.                          (GMR18)
```

The rank of left multiplication by `(GMR18)` is computed on the
right ideals cut by its two subgroup Fourier projections. There are

```text
|F_act|/|B|=384                B-character cosets,
|F_act|/|<k>|=2048             k-character cosets.
```

With these bases the matrix has size `384 by 2048`. A column indexed
by `<k>g` has at most three nonzero entries, in the rows represented by

```text
Bg,                 Bkg,                 Bk^2g,
```

with coefficients `1,omega^2,omega`, multiplied by the prescribed
`B` character when a canonical coset representative is changed.

Exact row reduction over `Q[omega]/(omega^2+omega+1)` gives

| `(sigma,tau)` | rows | columns | exact pivots |
|---|---:|---:|---:|
| `(+,+)` | 384 | 2048 | 344 |
| `(+,-)` | 384 | 2048 | 336 |
| `(-,+)` | 384 | 2048 | 336 |
| `(-,-)` | 384 | 2048 | 336 |

This table is reproducible directly from `(GMR9)` and `(GMR15)`: collect
the `6144` canonical coefficient triples, assign the `B` and `<k>`
cosets, insert the three entries just displayed, and eliminate using
`omega^2=-omega-1`. During this exact elimination every pivot row has at
most nine nonzero entries and every numerator and denominator has at most
three binary digits. Thus the pivot counts do not rely on reduction
modulo a prime or on a tolerance choice.

Finally the two selected central `h` characters double the active
ranks. Dividing by `(GMR17)` yields

```text
2*344/18432=43/1152                    for (+,+),

2*336/18432=7/192                      otherwise.        (GMR19)
```

If the ambient group is enlarged, its left regular representation
restricts to a direct sum of regular `F` modules, so these normalized
ranks are unchanged. Since

```text
1/18=64/1152,        43/1152<64/1152,
7/192=42/1152<64/1152,                               (GMR20)
```

the first `ST` return has no capacity excess.

The finite computation concerns the collected element `P` and its sign
envelope. It does not extend to a finite representation retaining the
raw equation `(GMR7)` with all of `g_2,U,V`: that larger constituent
group is precisely where the Jacobson one-sided relation survives. The
sharp next word must therefore leave both an uncancelled raw coefficient
and an uncancelled router leg after Steinberg collection.
