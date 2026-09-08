# Two copies of the first rank-one root orbit are impossible

2026-09-08. Suppose the finite packets `P,J` are represented
exactly and agree on their specified intersection `I`, as in
[the coherent correction proof](jacobson-first-root-packet-coherent-rounding-2026-09-08.md).
Retain the head and assume only that the first-braid defect is
strictly less than two. Then the nontrivial part of the `N` action
cannot consist of its rank-one character orbit with fiber dimension
two, even with an arbitrary `N`-trivial complement. Together with
the [fiber-one obstruction](jacobson-single-rank-one-orbit-obstruction-2026-09-08.md),
this raises the dimension bound to 147. It does not exclude larger
dimensions or establish a non-MF group.

## 1. Hypotheses and finite-character facts

Use the coherently glued finite packets

```text
P=N semidirect F,
N=Mat_(3 x 3)(F_2)_add,
F=G_Q x G_P,                 G=GL_3(F_2),
J=E semidirect (K_Q x G_*),
E=Hom(F_2^2,F_2^3),
I=N_0 semidirect (P_Q x K_P).
```

The head group `A_Q~=C_2^2` is normal in
`P_Q=A_Q semidirect K_Q~=S_4`. Each of `K_Q,K_P` is
`S_3`. The common root satisfies

```text
a=a_1=x_21,Q,       D=h a h in N,
b=w_23,Q w_23,P,    c=x_13,P,
||(h b)^3-I||<2.                                    (1)
```

Here and below words denote the matrices of the specified exact
representations. The last inequality says that the two involutions
`h b h` and `b h b` have distance less than two. Their negative
spectral projections have distance less than one and hence equal
ranks. They are conjugate to `b` and `h`, respectively. Since
`h,c` are conjugate in the exact shifted packet, this proves

```text
rank_-(a)=rank_-(D),           trace(c)=trace(b).      (2)
```

No exact mixed relator is assumed in the argument below.

We use the elementary character data proved in the appendix of
the fiber-one obstruction. The nontrivial irreducible `G`
representations have dimensions `3,3,6,7,8` and negative
involution ranks `2,2,2,4,4`. The group is perfect. For either
point or covector stabilizer `S~=S_4`, write

```text
rho_0=Ind_S^G(1),
rho_1=Ind_S^G(sgn),
rho_2=Ind_S^G(tau_2),
```

where `tau_2` is the two-dimensional representation of `S_4`
factoring through `S_4/V_4`. Their dimensions and involution
traces are

```text
representation       dimension       involution trace
rho_0                    7                   3
rho_1                    7                  -1
rho_2                   14                   2.     (3)
```

The following restrictions to `K~=S_3` will also be useful.
Write `tau` for its standard two-dimensional representation:

```text
G representation        restriction to K
1                       1
3 (either)              sgn + tau
6                       2*1 + 2*tau
7                       1 + 2*sgn + 2*tau
8                       1 + sgn + 3*tau.             (4)
```

These follow by evaluating the characters at the identity, an
involution, and an order-three element, using the elementary table
in that appendix. For the two three-dimensional representations,
their restriction to `S_4` is the sign twist of its standard
representation, which gives the displayed `S_3` restriction
directly. In particular every actual representation `V` of `G`
satisfies

```text
multiplicity_sgn(V|K)<=multiplicity_tau(V|K).         (5)
```

Finally, the head permutation representation has

```text
(rho_0)^(A_Q)=2*1 + tau                              (6)
```

under `K_Q`, and `rho_1|K_P=1+2*sgn+2*tau`.

## 2. The doubled orbit has a forced head and tail action

Suppose the whole nontrivial `N` part is the rank-one character
orbit with fiber dimension two. The orbit has 49 characters.
Each elementary root takes the value minus one on exactly 16
of them, so

```text
rank_-(D)=32.                                       (7)
```

The stabilizer of one rank-one character in `F` is
`S_Q x S_P~=S_4 x S_4`. Its fiber is a two-dimensional
representation of this product. Irreducibles of dimension at most
two are products of the trivial character, the sign character,
or the two-dimensional `tau_2`, with the product of the two
dimensions at most two.

If the head factor is trivial on both fiber dimensions, the head
negative rank on the induced orbit representation is 28. Any
nontrivial head action raises that rank to at least 42. To check
this explicitly, replacing one one-dimensional trivial head factor
by sign changes its induced negative rank from 14 to 28. A
two-dimensional head factor `tau_2`, with a one-dimensional
tail factor, gives negative rank

```text
(98-7*2)/2=42
```

by (3). A two-dimensional tail fiber with sign on the head gives
rank 56. These exhaust the decompositions of the two-dimensional
fiber. Equation (2) and (7) forbid ranks above 32. Therefore the
head stabilizer acts trivially on the fiber, and the restriction
of this 98-dimensional part to `F` is

```text
(rho_0)_Q tensor V_P,
V=Ind_(S_P)^G(chi),          dim(chi)=2.              (8)
```

The `N`-trivial complement consequently has head negative rank
exactly four. A tensor summand that is nontrivial on both `G`
factors would have head negative rank at least `2*3=6`, so no
such summand occurs. The entire complement has the form

```text
Sigma_Q tensor 1_P  direct-sum  1_Q tensor R_P,
rank_-(Sigma(a))=4,                                  (9)
```

where `R` is arbitrary and all nontrivial head constituents of
`Sigma` have trivial tail action. Any head-trivial constituents
can be absorbed into `R`.

On (8), the difference `trace(c)-trace(b)` is
`(7-3) trace(V(c))`. On the first summand of (9), it is
`2 rank_-(Sigma(a))=8`. On the second summand of (9), it
is zero, since the two relevant tail involutions are conjugate.
Thus (2) forces

```text
4 trace(V(c))+8=0,
trace(V(c))=-2.                                     (10)
```

The two-dimensional `S_4` representation `chi` is either a
sum of two linear characters or `tau_2`. By (3), the possible
involution traces of its induction are respectively `6,2,-2`
or `2`. Equation (10) therefore forces `chi=2*sgn`. We have
proved that the entire restriction to `F` is

```text
2*((rho_0)_Q tensor (rho_1)_P)
  direct-sum Sigma_Q tensor 1_P
  direct-sum 1_Q tensor R_P.                         (11)
```

## 3. The head fixed multiplicity space

Take `A_Q` fixed vectors and then the `tau_Q` isotypic part
under `K_Q`. Its multiplicity space is a representation of
`K_P`. By (6), each copy of `rho_0` in (11) contributes
one such multiplicity. The arbitrary head-trivial summand
contributes none. The `Sigma` summand has trivial tail action.
Thus for some nonnegative integer `t`, the full multiplicity
space supplied by `F` is

```text
M_F=(2+t)*1 + 4*sgn + 4*tau.                         (12)
```

The argument does not require a bound on `t` or a classification
of the possibilities for `Sigma` beyond (9).

Now decompose the same representation using the boundary root
group `E`. Its nonzero character orbits have ranks one and two,
with sizes 21 and 42. Let `m_1,m_2` be their common fiber
dimensions. The boundary root count and (7) give

```text
8m_1+24m_2=rank_-(a)=32,
(m_1,m_2)=(4,0) or (1,1).                            (13)
```

After computing the contribution of these nonzero characters to
(12), the remaining contribution comes from the `E`-trivial
subspace. That subspace is a representation of `K_Q x G_*`.
Its `tau_Q` multiplicity space is therefore an actual
representation of the full group `G_*`, and must satisfy (5)
on restriction to `K_P`.

## 4. Four-dimensional rank-one fibers are impossible

First take `(m_1,m_2)=(4,0)`. Write a rank-one boundary
character as `alpha tensor f`, where `alpha` is a nonzero
source vector and `f` a nonzero shifted target covector. Its
restriction to `A_Q` is zero precisely when `f(e_2)=0`.
These nine characters form one orbit under `K_Q x K_P`.

At a character with `f=e_1^*`, its full stabilizer in
`K_Q x G_*` is `C_2(source) x S_4(target)`. Its stabilizer
in `K_Q x K_P` is the product of two `C_2` groups. The target
involution is `x_31` and belongs to the normal four-group of
the target `S_4`.

The four-dimensional fiber, restricted to this `S_4`, is either
a sum of irreducibles of dimension at most two, or a
three-dimensional irreducible plus a linear character. The normal
four-group acts trivially on the former irreducibles. Its
nonidentity elements have negative rank two on either
three-dimensional irreducible. The positive and negative dimensions
of the target `C_2` action on the fiber are consequently

```text
(n_+,n_-)=(4,0) or (2,2).                            (14)
```

To obtain the contribution to the `tau_Q` multiplicity space,
induce this fiber from the two `C_2` stabilizers. Either linear
character of the source `C_2` induces to an `S_3`
representation containing exactly one `tau_Q`. Thus the source
signs do not affect the resulting multiplicity space. On the tail
side, induction of the trivial character is `1+tau`, and
induction of sign is `sgn+tau`. The nine characters contribute

```text
M_nonzero=n_+*1+n_-*sgn+4*tau.                       (15)
```

Subtracting (15) from (12), the remaining actual `G_*`
representation has zero `K_P` standard multiplicity and sign
multiplicity `4-n_-`, which is either four or two. This
contradicts (5). A negative trivial multiplicity would already be
a contradiction, but no such case distinction is needed.

## 5. A mixture of rank-one and rank-two fibers is impossible

It remains to consider `(m_1,m_2)=(1,1)`. For the rank-one
orbit, the preceding calculation with a one-dimensional fiber has
`n_+=1,n_-=0`, since every character of `S_4` kills its
normal four-group. Its contribution is

```text
M_rank_one=1+tau.                                   (16)
```

For the rank-two orbit, identify the dual boundary root space
with linear maps `lambda:F_2^3->F_2^2`. The characters fixed
by `A_Q` have `lambda(e_2)=0`. Rank two then says that the
restriction to the target plane `<e_1,e_3>` is invertible.
There are six such characters. The action of `K_Q x K_P`
on them is the left--right action on invertible two-by-two
matrices, with stabilizer a diagonal copy of `S_3` after
identifying the two factors.

The one-dimensional fiber restricts to either the trivial or the
sign character of this diagonal `S_3`. The corresponding induced
representations of `S_3 x S_3` are

```text
Ind_diag(1)   =1 tensor 1 + sgn tensor sgn + tau tensor tau,
Ind_diag(sgn) =1 tensor sgn + sgn tensor 1 + tau tensor tau.
```

For either choice, its `tau_Q` multiplicity space is exactly
`tau_P`. The rank-two contribution is therefore

```text
M_rank_two=tau.                                     (17)
```

Subtracting (16)--(17) from (12), the `E`-trivial multiplicity
space has restriction

```text
M_zero|K_P=(1+t)*1+4*sgn+2*tau.                      (18)
```

Its sign multiplicity exceeds its standard multiplicity. This
again contradicts (5), finishing both cases of (13).

We have excluded a sole rank-one `N` orbit with fiber dimension
two and an arbitrary `N`-trivial complement under the hypotheses
(1), using only exact finite packets and their shared words.

## 6. Dimension 147 and a numerical bound below it

The nonzero character orbits of `N` have sizes `49,168,294`.
The head is nontrivial only if `D=h a h` is nontrivial, so at
least one such orbit occurs. In dimension below 147, the only
possibilities are a rank-one orbit with fiber dimension one or
two, together with an arbitrary `N`-trivial complement. The
fiber-one proof also needs the braid only through the trace
equality (2), as detailed in Section 6 of the coherent correction
proof. Both possibilities are therefore excluded as soon as
the exact packets are coherently glued and their braid defect is
less than two. In particular every exact head-retaining
representation of `Xi` has dimension at least 147.

The same numerical constant from the coherent correction proof
now applies in dimensions at most 146. Indeed, for exact
compatible `F,J` with

```text
e=max(||W-I||,||(h b)^3-I||)
 <=1/18,259,771,392,
```

that proof corrects to exact compatible `P,J` on the same
dimension, holds `F` fixed, and gives corrected braid defect
less than two. The preceding obstruction rules this out in
dimension at most 146. Thus all such head-retaining models obey

```text
max(||W-I||,||(h b)^3-I||)>1/18,259,771,392
                          in dimensions d<=146.     (19)
```

The bound is approximately `5.48*10^(-11)`. Larger fibers and
the other nonzero `N` orbits remain unresolved. This finite
dimension bound does not imply a positive operator-norm gap over
all dimensions.
