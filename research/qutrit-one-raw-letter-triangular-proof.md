---
rg: 2
id: qutrit-one-raw-letter-triangular-proof
kind: route
title: Embed the one-letter head algebra in triangular polynomial matrices
target: qutrit-one-raw-letter-head-router-is-residually-finite
requires:
  - qutrit-two-scalar-routers-leave-head-packet-finite
  - qutrit-third-cell-head-selector-is-h-centralizer-zero
  - depth-mismatched-qutrit-root-bridge-is-residually-finite
---

## Presentations and normal forms

Write `q=s_1t_1=1-s_0t_0`. The Leavitt relations give

```text
q^2=q,
t_0q=0,                    t_1q=t_1,                     (QRL8)
qs_0=0,                    qs_1=s_1.
```

Fix `r` and put `epsilon=delta_(r1)`. In the abstract algebra

```text
B_epsilon=F_2<q,t | q^2=q, tq=epsilon t>,
```

every word reduces to the span of

```text
1,        t^n (n>=1),        q t^n (n>=0).              (QRL9)
```

Indeed a `q` occurring after a `t` is either deleted or kills the word,
and adjacent copies of `q` merge.

There are no further relations after mapping `t` to `t_r` in `L`.
Suppose a finite linear combination of the words in `(QRL9)` vanishes.

For `r=0`, left multiplication by `t_0` kills every `qt_0^n` term
and leaves a linear combination of the distinct negative paths
`t_0,t_0^2,...`. Thus every coefficient of `1,t_0^n` is zero. Left
multiplication of the remaining relation by `t_1` sends
`qt_0^n` to the distinct negative paths `t_1t_0^n`, so all remaining
coefficients vanish.

For `r=1`, left multiplication by `t_1` identifies the coefficient of
each `t_1^n` with the corresponding coefficient of `qt_1^n`. Left
multiplication of the original relation by `t_0` kills all `q` terms
and leaves the distinct paths `t_0t_1^n`, forcing the first family of
coefficients to vanish; the identified second family then vanishes too.
Linear independence of distinct pure negative paths is the standard
Leavitt normal form. This proves `(QRL1)`.

The Leavitt anti-involution interchanging `s_i` and `t_i` fixes `q`.
It gives the asserted anti-isomorphic presentations for `A_r^+`.

## Polynomial matrix embeddings

For `epsilon=0` define

```text
q |-> [[1,0],[0,0]],       t |-> [[0,1],[0,x]].          (QRL10)
```

Then `q^2=q` and `tq=0`. For `n>=1`,

```text
t^n   |-> [[0,x^(n-1)],[0,x^n]],
qt^n  |-> [[0,x^(n-1)],[0,0]].
```

These matrices, together with `1,q`, have exactly the independence in
`(QRL9)`.

For `epsilon=1` use

```text
q |-> [[1,0],[0,0]],       t |-> [[x,0],[1,0]].          (QRL11)
```

Now `tq=t`, and

```text
t^n   |-> [[x^n,0],[x^(n-1),0]],
qt^n  |-> [[x^n,0],[0,0]].
```

Again the normal words are linearly independent. Equations
`(QRL10)--(QRL11)` prove the claimed embeddings. Transpose after applying
the anti-involution gives the positive-letter embeddings.

If a polynomial matrix is nonzero, reduction modulo `x^N` with `N`
larger than every degree occurring in a nonzero entry keeps it nonzero.
Since `F_2[x]/(x^N)` is finite, each `A_r^plus-or-minus` is residually
finite as an algebra.

## Elementary-group closure and residual finiteness

The scalar group `K` moves `H` to every `q`-labelled root and `T_r`
to every `t_r`-labelled root. Root additivity and three-index
commutators generate sums and products, hence every root labelled by
`A_r^-`. Conversely every generator is elementary over that algebra.
Therefore

```text
<K,H,T_r>=EL_28(A_r^-).                                 (QRL12)
```

The ring embedding in `M_2(F_2[x])` induces an injective matrix-group
map

```text
EL_28(A_r^-) -> GL_56(F_2[x]).                           (QRL13)
```

For a nonidentity group element, choose `N` above the degrees in one
nonzero entry of its difference from the identity. Reduction modulo
`x^N` maps it nontrivially into the unit group of the finite ring
`M_56(F_2[x]/(x^N))`. This proves residual finiteness. The same proof
works for `A_r^+`.

The presentations in `(QRL1)` are finite unital ring presentations.
The Krstic--McCool theorem makes `EL_28(A_r^plus-or-minus)` finitely
presented.

## The two shortest head words

Take the root positions

```text
H=x_(c_2,c_1)(q),              T_r=x_(c_3,c_2)(t_r).
```

The Steinberg relation and `(QRL8)` give

```text
[T_0,H]=1,
[T_1,H]=x_(c_3,c_1)(t_1)=B_1.                           (QRL14)
```

For `r=0`, `T_0` commutes with `H`, so `ET_0E=T_0E` is unitary on
the full `E` corner.

For `r=1`, the three involutions `H,T_1,B_1` form `D_8`. Exactly as in
the third-cell calculation,

```text
(ET_1E)^2=F_+=E(1+B_1)/2.                               (QRL15)
```

The projection `F_+` carries half of each qutrit atom. Since the
support of `g_1` is disjoint from `c_1,c_2,c_3`, it commutes with
`H,T_r`. Therefore

```text
||g_1ET_0ER||_2^2=tau(ER)=1/9,
||g_1ET_1ER||_2^2=tau(F_+R)=1/18.                       (QRL16)
```

This is `(QRL6)`.

## Exact routed norm on the killed branch

Put `v=g_1T_0`. We first compute its intersection with `C`. Suppose
`c=vc'v^(-1)` with `c,c' in C`. Since `g_1` is scalar,

```text
T_0c'T_0^(-1)=g_1^(-1)cg_1
```

is a scalar matrix. Comparing the coefficient of `t_0` in the raw-root
conjugation forces `c'` to fix the two endpoints `c_3,c_2`. Thus
`T_0` commutes with `c'`. We are left with
`c=g_1c'g_1^(-1)`, and `C intersect g_1Cg_1^(-1)={1}`
forces `c'=c=1`. Hence

```text
C intersect vCv^(-1)={1}.                               (QRL17)
```

The head `H` commutes with `C` and `v` and is independent of the
scalar/different-coefficient subgroup. Thus its cut `E` halves every
complete Hecke block. Equations `(QRL17)` and the double-coset formula
give

```text
||e_2vEe_a||_2^2=1/162,                 a=0,1.
```

The two right supports are orthogonal, proving

```text
||e_2g_1T_0ER||_2^2=1/81.                               (QRL18)
```

The target polar remains below `Ee_2`, of trace `1/18`. The raw
`t_0` letter has not repaired the missing half of the `ER` source.

For the surviving branch, `(QRL16)` already shows that the D8
compression has energy `1/18` before the final qutrit target cut. It
cannot create a source larger than the one-complement capacity.

## Finite regular countermodels

Residual finiteness is enough to preserve any prescribed finite audit.
Choose a finite quotient which is injective on `C` and separates every
nonidentity group word occurring in the expansions of
`(QRL14)--(QRL18)`. Its left regular representation has uniform
`C`-character weights `1/9` and the same identity coefficients in all
those expansions. Hence all displayed traces and norms hold exactly in a
finite-dimensional representation with `H!=1`.

The full Leavitt group has additional positive and negative letters and
kills `H` in finite-dimensional representations. This proof shows that
neither one negative letter nor, by anti-isomorphism, one positive letter
can be responsible. The first eligible relation must mix the two
orientations outside a common triangular polynomial chart.
