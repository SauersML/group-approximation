---
rg: 2
id: two-qutrit-common-intertwiner-firewall-proof
kind: route
title: Compress the packet at the active atom and telescope one common intertwiner
target: two-qutrit-common-intertwiner-is-scalar-or-universal
requires:
  - two-qutrit-and-atom-has-no-internal-joint-frame
  - two-qutrit-and-cell-retains-sectorwise-pauli-gauge
---

For `a=b=0`, the character projection in the two-qutrit construction is

```text
p=(1/27) sum_(c,v,t in F_3)
      omega^(-c) J^c Z_1^v Z_2^t.                      (TCIP1)
```

In the marked spin representation choose the standard basis `|i,j>`, with
`Z_1|i,j>=omega^i|i,j>` and `Z_2|i,j>=omega^j|i,j>`. Then `(TCIP1)`
is `|0,0><0,0|`. A normal-form element

```text
g=J^c X_1^u Z_1^v X_2^s Z_2^t
```

sends `|0,0>` to a scalar multiple of `|u,s>`. Its compression to
`C|0,0>` is therefore zero unless `u=s=0`. In the remaining case the two
`Z` powers act by one and `J^c` acts by `omega^c`, proving `(TCI1)`.
Linearity proves `p C[F]p=Cp`.

On an isotypic carrier the packet representation is

```text
x |-> pi_spin(x) tensor I_M.
```

Hence every packet coefficient compressed on both sides by `p tensor I_M`
is a scalar multiple of `p tensor I_M`. If such a coefficient is a
projection below `p tensor I_M`, its scalar is zero or one. This proves the
packet-minimality and nontransport assertions.

We prove the common-intertwiner estimate with the group-commutator convention

```text
[C,D]=C D C^* D^*.                                      (TCIP2)
```

Let `tau` be the normalized matrix trace and
`||x||_2=tau(x^*x)^(1/2)`. Write

```text
e_A=A^o w-wA,                 e_B=B^o w-wB.             (TCIP3)
```

Since all four actors are unitaries, the adjoint intertwining defects have
the same norms. Indeed,

```text
(A^o)^*w-wA^*=-(A^o)^* e_A A^*,
(B^o)^*w-wB^*=-(B^o)^* e_B B^*.                        (TCIP4)
```

Telescope the four letters in the order fixed by `(TCIP2)`:

```text
[A^o,B^o]w-w[A,B]
 =A^o B^o (A^o)^*((B^o)^*w-wB^*)
  +A^o B^o((A^o)^*w-wA^*)B^*
  +A^o(B^o w-wB)A^*B^*
  +(A^o w-wA)BA^*B^*.                                  (TCIP5)
```

Every exterior factor in `(TCIP5)` is unitary. Equations
`(TCIP3)--(TCIP4)` and the triangle inequality give

```text
||[A^o,B^o]w-w[A,B]||_2<=2 delta_A+2 delta_B.           (TCIP6)
```

Because `ww^*=s` and `s` reduces `A^o,B^o`, traciality gives

```text
||([A^o,B^o]-1)w||_2^2
 =tau(w^*([A^o,B^o]-1)^*([A^o,B^o]-1)w)
 =tau((([A^o,B^o]-1)s)^*(([A^o,B^o]-1)s))
 =delta_0^2.                                            (TCIP7)
```

Finally,

```text
w([A,B]-1)
 =(w[A,B]-[A^o,B^o]w)+([A^o,B^o]-1)w.
```

Combining `(TCIP6)--(TCIP7)` proves `(TCI4)`.

In the active Pauli escape, `[A,B]r=-r` and `w=wr`. Therefore

```text
w([A,B]-1)=-2w,
||w([A,B]-1)||_2^2=4 tau(w^*w)=4 tau(r),                (TCIP8)
```

which proves `(TCI5)`. With zero defects, positive `r` is impossible.
No finite-dimensional step was used in `(TCIP3)--(TCIP8)` beyond choosing
a normalized trace. The same calculation holds in every tracial C-star
algebra, proving the universal-lock scope and showing why the missing
positive occurrence must be extracted specifically from finite matrix
coordinates rather than imposed as the displayed exact common-arrow rows.
