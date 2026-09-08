# A rank gap for literal finite coefficient realizations

2026-09-08. Handwritten block and nullity proof, independently audited.
No numerical experiment is used. This excludes a coefficient ansatz;
it does not prove a gap for arbitrary complex unitary models.

## 1. Retain the coefficient defect

Let `K` have characteristic two, let `s,t,v in M_d(K)`, and put
`Z=ts`. Take the coordinate cycle `c` with `e_1 -> e_2 -> e_3 -> e_1`
and `b_1=x_12(s)`, `b_2=x_12(t)`, `b_3=x_12(v)`.
All three `b_i` commute and square to the identity, whether or not
their coefficients are independent. Use the packet's words

```text
gamma=Ad(c),                 d_word=[b_2,gamma(b_1)],
h=gamma^2(d_word),           a=[d_word,h],
e=gamma(d_word),             j=a e a^(-1),
u=[b_2,gamma(b_3)],          w=[gamma^2(b_1),a],
r_*=j c j c,                R_v=[b_3,gamma(b_3)]d_word^(-1),
R_0=[u,w].
```

The distinct-index commutator formula gives

```text
d_word=x_13(Z), h=x_32(Z), a=x_12(Z^2), e=x_21(Z),
u=x_13(tv), w=x_32(sZ^2),
R_v=x_13(v^2+Z), R_0=x_12(tvsZ^2).                 (RG1)
```

No use of `ts=1` has been made. Since `a^(-1)=a`, direct block
multiplication gives

```text
j = [ I+Z^3  Z^5    0 ]       jc = [ Z^5    0  I+Z^3 ]
    [ Z      I+Z^3  0 ]            [ I+Z^3  0  Z     ]
    [ 0      0      I ]            [ 0      I  0     ].
```

In particular

```text
(r_*-I)_(3,3)=((jc)^2-I)_(3,3)=Z-I.                (RG2)
```

Every entry in the multiplication is a power of the same `Z`, so
no commutativity of the separate coefficients is assumed.

## 2. The quantitative rank obstruction

Set

```text
r=rank(Z-I), q=rank(v^2+Z), p=rank(tvsZ^2).
```

First, `rank Z>=d-r`, and `rank t>=rank(ts)=rank Z`, so
`nullity t<=r`. Also, in characteristic two,

```text
rank(v^2-I)<=rank(v^2+Z)+rank(Z-I)=q+r,
rank v>=rank(v^2)>=d-q-r.                           (RG3)
```

On the subspace `E=ker(Z-I)`, the map `sZ^2` is injective.
Indeed, for `x in E`, `Z^2x=x`. If `sZ^2x=0`, then `sx=0`
and hence `x=Zx=tsx=0`. Thus

```text
rank(sZ^2)>=dim E=d-r,
nullity(sZ^2)<=r.                                  (RG4)
```

For square matrices of size `d`, the rank inequality
`rank(ABC)>=rank B-nullity A-nullity C` follows by applying
`rank(XY)>=rank X+rank Y-d` twice. Apply it with
`A=t`, `B=v`, `C=sZ^2`. Equations (RG3)--(RG4) give

```text
p>=d-q-3r,                 p+q+3r>=d.              (RG5)
```

Taking a block cannot increase rank, so (RG2) gives
`r<=rank(r_*-I)`. Equation (RG1) identifies the full ranks
of `R_v-I` and `R_0-I` with `q` and `p`. Consequently

```text
rank(R_0-I)+rank(R_v-I)+3 rank(r_*-I)>=d.
```

Divide by the ambient dimension `3d`. If the maximum of the
three normalized ranks is `M`, then `5M>=1/3`, proving
`M>=1/15`. The fourth packet word `R_sum` is unnecessary for
this coefficient-class obstruction.

## 3. Exact directly finite coefficient rings

The block identities also hold for `s,t,v` in an arbitrary unital
ring of characteristic two. Recall that direct finiteness means
`xy=1` implies `yx=1`. If all three words are identity, (RG2)
gives `ts=1`; direct finiteness then gives `st=1`.
Equation (RG1) gives `v^2=1` and `tvs=0`. But

```text
s(tvs)t=(st)v(st)=v,
```

so `v=0`, contradicting `v^2=1` in any nonzero ring.
This covers finite coefficient rings as well: on a finite ring,
`ts=1` makes left multiplication by `s` injective and hence
surjective, giving a right inverse for `s`, which must equal `t`.

## 4. What this does and does not transfer

The claim applies to literal elementary matrices over coefficients
with one common finite-dimensional vector space, and the exact
claim applies to directly finite coefficient rings. It neither
identifies arbitrary abstract word values with such coefficients
nor compares rank distance in characteristic two with normalized
Hilbert--Schmidt distance in complex representations.

The missing issue can also be expressed on a finite elementary
abelian receiver `A`: if globally defined endomorphisms `S,T,V`
satisfy `TS=id`, `V^2=id`, and `TVS=0` on all of `A`, then
`S,T,V` are bijective and `TVS` cannot be zero unless `A=0`.
One must first construct this common additive receiver and prove
the identities on all of it. The finite group-word packet alone
does not provide that construction or propagation argument.

The unrestricted `24k` normalized-HS gap and the opposite
vanishing branch both remain open.
