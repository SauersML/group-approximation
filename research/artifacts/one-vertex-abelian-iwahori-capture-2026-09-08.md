# Explicit capture from one nearly commuting modular vertex

2026-09-08. The argument constructs an endpoint from two Iwahori edge
errors and one internal commutator. It does not assume that the second
vertex commutes, that the vertices commute with each other, or that their
central involutions agree. The same endpoint satisfies simultaneous
dimension-free bounds in every normalized Schatten norm, including the
operator norm. This is a restricted capture theorem, not general flexible
stability or a non-hyperlinear group construction.

## 1. Exact relations and the quantities used

Let the two vertices obey

```text
S_i^4=I,             S_i^2=B_i^3=Z_i.
```

The common power `Z_i` is central in its own vertex, and `Z_i^2=I`.
Write

```text
T_i=S_i^(-1)B_i,
L_i=S_i T_i^(-1) S_i^(-1)=S_i B_i^(-1).
```

These are the upper and lower unipotents of that modular vertex. The
two noncentral edge equations are `T_1=T_2^2` and `L_1^2=L_2`.
For any one norm in the theorem put

```text
a=||T_1-T_2^2||,
b=||L_1^2-L_2||,
k=||S_1B_1-B_1S_1||.
```

All estimates below use only unitary invariance and the triangle
inequality, except for the explicitly proved spectral rounding bound.
Thus the same calculation applies to each normalized Schatten norm
and to operator norm without changing constants or matrices.

## 2. The fifteenth-power estimate

The first commutator gives

```text
||L_1-T_1^(-1)||=k.
```

Two power telescopings and the lower edge equation give

```text
||L_2-T_2^(-4)|| <= b+2k+2a =: d.                    (1)
```

Let `A=Ad(S_2)`. Inverting the two unitaries in (1) yields

```text
||A(T_2)-T_2^4||<=d.                                (2)
```

Since `S_2^2=Z_2` commutes exactly with `T_2`, one has
`A^2(T_2)=T_2`. Apply `A` to (2), and telescope the fourth power
of (2), to obtain

```text
||T_2-T_2^16||<=d+4d=5d,
||T_2^15-I||<=5d.                                   (3)
```

No relation between `Z_1` and `Z_2` has been used.

## 3. The twenty-fourth-power estimate and the cubic consequence

For any modular vertex with commutator norm `k_i`, moving the three
out-of-order pairs in `(S_i^(-1)B_i)^3` costs at most `3k_i`.
Indeed commuting `S_i^(-1)` past `B_i` costs exactly `k_i`, and
all other factors are unitary. The exact common power then gives

```text
||T_i^3-S_i^(-3)B_i^3||<=3k_i,
S_i^(-3)B_i^3=S_i^(-1).                             (4)
```

For the first vertex, raise (4) to the fourth power. Since `S_1^4=I`,

```text
||T_1^12-I||<=12k.
```

The upper edge equation consequently implies

```text
||T_2^24-I||<=12(a+k).                              (5)
```

The exact integer identity `3=2*24-3*15` now gives, using powers of
the same unitary throughout,

```text
||T_2^3-I||
 <=2||T_2^24-I||+3||T_2^15-I||
 <=24(a+k)+15d
 =54a+15b+54k =: r.                                 (6)
```

## 4. Both modular order-four generators become small

The second internal commutator is controlled, despite not being an
assumption:

```text
k_2:=||S_2B_2-B_2S_2||
    =||A(T_2)-T_2||
    <=d+||T_2^4-T_2||<=d+r.                         (7)
```

Apply (4) to the second vertex and combine with (6):

```text
s_2:=||S_2-I||<=3k_2+r<=3d+4r.                     (8)
```

The upper edge also gives `||T_1^3-T_2^6||<=3a`. Therefore

```text
||T_1^3-I||<=3a+2r,
s_1:=||S_1-I||<=3k+3a+2r.                          (9)
```

These bounds control the full order-four generators; no positive-central
restriction or compatible comparison was supplied.

## 5. One rounding map works in all the norms

For each spectral value `z` of `T_2`, choose a nearest cube root
`c(z)`, with one fixed choice at a tie. Put `C=c(T_2)`, so `C^3=I`.
Write `z=c(z)e^(it)` with `|t|<=pi/3`. If `t!=0`, then

```text
|z-c(z)|/|z^3-1|
 = |sin(t/2)|/|sin(3t/2)|
 = 1/(3-4sin^2(t/2)) <=1/2.                         (10)
```

The inequality is also valid at `t=0`, where both differences vanish.
Spectral calculus gives, for this single choice of `C`,

```text
||C-T_2||_p <= (1/2)||T_2^3-I||_p <=r_p/2            (11)
```

for every `1<=p<=infinity`. The fixed tie choice does not affect this
estimate or the endpoint identities.

Take the endpoint

```text
(S_1',B_1',S_2',B_2')=(I,C^2,I,C).                  (12)
```

Its modular relations are exact and both central involutions are the
identity. At this endpoint, `T_1'=C^2=(T_2')^2`, while
`(L_1')^2=C^2=L_2'`. It is therefore exactly Iwahori compatible.

Since `B_i=S_i T_i`, equations (8)--(11) give

```text
||B_2-C|| <= s_2+r/2 <=3d+(9/2)r,
||B_1-C^2|| <= s_1+a+r <=3k+4a+3r.                  (13)
```

The first bound dominates the second: their difference is
`2a+3b+3k+(3/2)r>=0`. It also dominates the bounds for both `S_i`.
Consequently

```text
max_U ||U'-U||
 <=3d+(9/2)r
 =249(a+k)+(141/2)b
 <=320(max(a,b)+k).                                 (14)
```

This proves the theorem simultaneously in all the stated norms, using
the same endpoint (12).

## 6. What would and would not follow

If the first vertex commutes exactly, `k=0`; the two edge errors alone
then give a same-dimensional linear repair, even if the second vertex
or the cross-vertex commutators initially fail to commute. If both edge
errors and `k` vanish exactly, the argument forces
`S_1=S_2=I`, `B_1=B_2^2`, and `B_2^3=I`. The group-theoretic quotient
obtained by making the first vertex abelian is thus cyclic of order
dividing three, and (14) is an explicit quantitative version.

For general small-defect pairs, `k` need not be small: an exact
nonabelian compatible quotient can have a nonzero first-vertex
commutator. Thus (14) does not prove unrestricted capture. It supplies
no small-rank bound for the full endpoint change; two very close
finite-order matrices can have a full-rank difference. The support
surgery and the low-singular-residual approach remain separate tools
for inputs outside this class.

The word estimates and constants were independently checked by the
root and charge agents. No numerical experiment is a prerequisite for
the argument.
