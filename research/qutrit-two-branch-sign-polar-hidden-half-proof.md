---
rg: 2
id: qutrit-two-branch-sign-polar-hidden-half-proof
kind: proof
title: Count the extra branch sign and the nine-dimensional Cuntz-chain absorber
target: qutrit-two-branch-sign-polar-has-hidden-half-absorber
requires:
  - qutrit-jacobson-sign-polar-rank-proof
  - qutrit-complementary-sign-finite-router-proof
  - qutrit-parallel-cuntz-cell-finite-packet-proof
---

## 1. The literal two-branch chain

The Leavitt relations give

```text
t_r s_s=delta_(rs),              r,s in {0,1}.
```

Applying the three-index Steinberg relation to `(QBH1)` yields

```text
[H,U_r]=A_r=x_(c_2,c_0)(qt_r),
[U_r,V_s]=x_(c_1,c_3)(t_rs_s),
[A_r,V_s]=x_(c_2,c_3)(qt_rs_s).                         (QBH8)
```

Thus the last two rows are respectively the scalar root and `W` when
`r=s`, and the identity when `r!=s`. This proves `(QBH2)`.

The relevant involutions commute except for the displayed Heisenberg
pairs. In particular `H,A_0,A_1,W` commute, and

```text
U_r H U_r=H A_r,
V_r A_r V_r=A_r W.                                     (QBH9)
```

For `r!=s`, the second conjugation fixes `A_r`.

## 2. Exact compressed polar supports

Fix `G=G_(sigma,tau)`. The operator `G U_0 G` is self-adjoint. Using
`(QBH9)` and the facts that `H=-1` and `A_0=sigma` on `G`,

```text
(G U_0 G)^2
 =G                         if sigma=+,
 =0                         if sigma=-.                 (QBH10)
```

Likewise `V_0` conjugates the `A_0` sign to the `A_0W` sign and fixes
the other defining signs of `G`. Therefore

```text
(G V_0 G)^2
 =G                         if tau=+,
 =0                         if tau=-.                   (QBH11)
```

The original branch preserves the full selected sign carrier only at
`(sigma,tau)=(+,+)`.

The new root `A_1` commutes with every defining involution of `G`.
Equation `(QBH9)` gives

```text
(G U_1 G)^2=G(1+A_1)/2.                                 (QBH12)
```

For `tau=+` this right side is `P_sigma`. Since `V_1` commutes with
`H,A_0,W` and sends `A_1` to `A_1W`,

```text
(P_sigma V_1 P_sigma)^2
 =P_sigma(1+W)/2
 =P_sigma.                                               (QBH13)
```

If `tau=-`, the same calculation gives zero. Equations
`(QBH10)--(QBH13)` prove the support table in the claim. They are
support identities, not Hilbert--Schmidt energy comparisons.

Let `R=e_0+e_1`. Put `X=G U_1 G` in the surviving row. Since
`X^*X=P_sigma`,

```text
(XR)^*(XR)=R P_sigma R.                                 (QBH14)
```

Thus the source support of the literal complementary-branch compression
has exactly the rank of `P_sigma R`. The second compression by `V_1`
is unitary on `P_sigma` and causes no further loss. Since
`P_sigma<=G_(sigma,+)`, the complementary source is nested in the
original source; it is not an orthogonal second copy.

## 3. Rank of the hidden-sign cut

Let

```text
F_1=<C,H,A_0,A_1,W>.
```

The three root labels `qt_0,qt_1,q` are linearly independent in the
positions used in `(QBH1)`. Under `C/<h> isomorphic to C_3`, the
normal closure of each of `A_0,A_1,W` is one copy of the irreducible
two-dimensional `F_2[C_3]` module `V`. The three copies commute and
are independent. Hence

```text
F_1 isomorphic to <H> times <h> times
                  ((V direct-sum V direct-sum V) semidirect C_3),
|F_1|=2*3*2^6*3=1152.                                  (QBH15)
```

As in the two-sign rank calculation, `R` selects two central
`<h>` characters and one fixed quotient `C_3` character. It remains
to compute the rank of one three-sign projection against that quotient
character in

```text
G_1=F_2^6 semidirect C_3,             |G_1|=192.        (QBH16)
```

Identify the dual of `V^3` with `F_4^3` and let
`F_4^times=C_3` act by common scalar multiplication. There are

```text
(4^3-1)/3=21
```

nonzero character orbits, hence twenty-one induced three-dimensional
irreducibles, together with three one-dimensional quotient characters.

Every one of the eight signs of
`B=<A_0,W,A_1>` is met by exactly seven of the twenty-one orbits. Here
is a short count. For a projective point `[x_0:x_1:x_2]`, the three
scalar multiples have restrictions

```text
lambda |-> (Tr(lambda x_0),Tr(lambda x_1),Tr(lambda x_2))
              in F_2^3.
```

The map has rank one at the seven `F_2`-rational projective points and
rank two at the other fourteen points. Thus the zero sign occurs at the
seven rank-one points. The number of incidences with nonzero signs is

```text
7*1+14*3=49.
```

The group `GL_3(F_2)` is transitive on the seven nonzero signs, so every
nonzero sign also occurs at exactly seven projective points.

In each induced three-dimensional representation, multiplying the sign
projection by the selected quotient Fourier projection has rank one
exactly when that orbit meets the sign. The regular multiplicity is
three. The induced representations therefore contribute rank `7*3=21`
for every sign. Exactly one one-dimensional quotient character is
selected, and it contributes only to the all-plus sign. Hence the
regular `G_1` ranks are

```text
22 for the all-plus sign,             21 for every other sign.   (QBH17)
```

The two selected `<h>` blocks double these numbers. Dividing by
`|F_1|=1152` gives

```text
tau(supp|P_+R|)=44/1152=11/288,
tau(supp|P_-R|)=42/1152=7/192.                          (QBH18)
```

Together with the previously computed ranks
`5/72` and `1/16` for `G_(sigma,+)R`, this proves `(QBH5)`.
Since

```text
tau(Ee_2)=1/18=16/288=32/576,
```

the complementary-branch capacity margins are

```text
1/18-11/288=5/288,
1/18-7/192=11/576.                                     (QBH19)
```

There is no second Hall deficit.

## 4. The finite absorber

Before torus closure, use the ordered coordinate path

```text
c_2 -> c_1 -> c_0 -> c_3.
```

Let `mathcal N` be the strictly upper-triangular coefficient algebra
with spaces

```text
(c_2,c_1): F_2 q,                dimension 1,
(c_1,c_0): span{t_0,t_1},        dimension 2,
(c_0,c_3): span{s_0,s_1},        dimension 2,
(c_2,c_0): span{qt_0,qt_1},      dimension 2,
(c_1,c_3): F_2,                  dimension 1,
(c_2,c_3): F_2 q.                dimension 1.            (QBH20)
```

The only coefficient products are those along this path, and `(QBH8)`
shows that they remain in the displayed spaces. Therefore

```text
dim_(F_2)(mathcal N)=9,             mathcal N^4=0.
```

The five roots `H,U_0,U_1,V_0,V_1` and their commutators generate every
displayed direction. Ordered root collection gives

```text
<H,U_0,U_1,V_0,V_1>=1+mathcal N,
|1+mathcal N|=2^9.                                      (QBH21)
```

Now enlarge each coordinate to its full `C`-invariant scalar summand.
The torus preserves the four-stage flag. The minimal router
`g_1=(c_0 d_0 d_1)` only enlarges the middle stage and still preserves
that flag. The span of all `<C,g_1>` conjugates of `mathcal N` and
their products is finite-dimensional and fourth-power zero. Hence

```text
<C,g_1,H,U_0,U_1,V_0,V_1>
```

is finite. Its regular representation restricts to a multiple of the
regular representation of `F_1`, so every rank in `(QBH18)` is realized
literally while `H` remains nonidentity.

This proves the finite absorber and the stated boundary. The first
unabsorbed test must use `g_2` in the same support-preserving word; adding
the two raw branches as a separate finite packet cannot force the desired
target return.
