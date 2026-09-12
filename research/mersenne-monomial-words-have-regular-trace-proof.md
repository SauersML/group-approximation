---
rg: 2
id: mersenne-monomial-words-have-regular-trace-proof
kind: route
title: Read every fixed word through its monomial permutation and van Kampen area
target: mersenne-diagonal-countersequence-is-tracially-regular
requires:
  - mersenne-phases-refute-diagonal-iwahori-decoder
---

Write `d_n=|Q_n|` and use the normalized norm

```text
||A||_(2,d)=(Tr(A* A)/d)^(1/2).
```

Every marked generator in `U_n=(X_n,R_n,T_n)` is monomial:
`R_n` and `T_n` are regular permutation matrices, while

```text
X_n=M_((-1)^c_n) lambda_(Q_n)(x).
```

Consequently, for each fixed word `w=w(x,r,t)`, multiplication of
monomial matrices gives

```text
w(U_n)=M_(sigma_(n,w)) lambda_(Q_n)(q_n(g_w)),           (MWT1)
```

where `sigma_(n,w):Q_n->{+1,-1}`, `g_w` is the element represented by
`w` in `PSL_2(Z[1/2])`, and `q_n` is reduction modulo
`m_n=4^n-1`.

Suppose first that `g_w` is nontrivial. Choose a representative
`A in SL_2(Z[1/2])`. If `q_n(g_w)=1` for infinitely many `n`, then
for each of those `n` one has

```text
A=epsilon_n I (mod m_n),  epsilon_n in {+1,-1}.          (MWT2)
```

After passing to one sign and clearing a fixed power-of-two denominator,
every entry of one fixed nonzero integral matrix
`2^s(A-epsilon I)` is divisible by the unbounded integers `m_n`.
That is impossible. Thus `q_n(g_w)` is nontrivial for all sufficiently
large `n`. A nonidentity left translation of `Q_n` has no fixed basis
vector, so the signed monomial matrix in (MWT1) has zero diagonal.
Therefore

```text
tr_(Q_n)(w(U_n))=0                                      (MWT3)
```

eventually.

Now suppose that `g_w=1`. Fix once and for all an expression of `w`
as a product of conjugates of the relators in the square-free
presentation

```text
<x,r,t | x^2,(xr)^2,(xt)^3,rtr^(-1)t^(-4),
           (xt^2r)^3>.
```

On `U_n`, the involution, inversion, and fourth-power relators are
exact. Put

```text
e_(a,n)=||(X_nT_n)^3-1||_2,
e_(b,n)=||(X_nT_n^2R_n)^3-1||_2.
```

Unitary invariance and telescoping along the fixed relator expression
give a constant `C_w<infinity`, independent of `n`, such that

```text
||w(U_n)-1||_2
 <= C_w (e_(a,n)^2+e_(b,n)^2)^(1/2)
 < C_w sqrt(24/n).                                     (MWT4)
```

The normalized trace is dominated by normalized Hilbert--Schmidt norm,
so (MWT4) implies

```text
tr_(Q_n)(w(U_n))->1.                                    (MWT5)
```

Equations (MWT3) and (MWT5) prove (MTR1).

For completeness, both flexibility assertions follow directly at the
word level. If `k_n=o(d_n)` arbitrary dimensions carrying any unitary
tuple `W_n` are adjoined, then for each fixed word

```text
|tr_(d_n+k_n)(w(U_n direct-sum W_n))-tr_(d_n)(w(U_n))|
 <=2k_n/(d_n+k_n)=o(1).                                (MWT6)
```

More generally, let `Y_n` act on a space of dimension `D_n>=d_n`,
let `V_n:C^(d_n)->C^(D_n)` be an isometry, assume
`D_n/d_n->1), and assume for each marked generator `s` that

```text
||Y_(s,n)V_n-V_nU_(s,n)||_(2,d_n)->0.                   (MWT7)
```

Telescoping a fixed word gives

```text
||w(Y_n)V_n-V_nw(U_n)||_(2,d_n)->0.                     (MWT8)
```

With `P_n=V_nV_n*`, (MWT8) compares the normalized trace on the
`P_n)-corner to that of `w(U_n)). For every contraction `A` on the
`D_n)-space,

```text
|Tr(P_nA)/d_n-Tr(A)/D_n|
 <=2(D_n-d_n)/D_n.                                     (MWT9)
```

Applying (MWT9) to `A=w(Y_n)` proves that every fixed-word trace has
the same limit. This covers almost-full generalized-HS replacement and
proves the stated trace firewall. It deliberately supplies no
operator-norm, Hamming, or full-endpoint obstruction.
