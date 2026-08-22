---
rg: 2
id: atlas-q14-adds-stratified-thirteenth-double-coset
kind: claim
title: Adding q14 turns the common-U system into twelve packet products plus one stratified involution double coset
distinct_from:
  atlas-common-u-is-twelve-double-coset-system: that gives the packet and 19243 system; this adds q14 in the same total-frame coordinate and classifies its exact locus.
  atlas-q14-forces-t30-covariance-floor: that proves the quantitative t30 wall from q14; this identifies the full exact q14 solution set and proves it leaves every packet witness gauge untouched.
  atlas-a4-root-energy-ellipse-ceiling: that seeks an upper bound from packet plus 19243; this supplies the opposite sharp lower wall in the augmented kernel menu.
---

Let `D=20160k`, `rho=Reg(A8) tensor I_k`, and retain the total common frame
`W` and reference alignment `R` from the twelve-double-coset system.  Put

```text
a=rho(t23),
h=R a R^*=rho(t30),
V=W R^*.                                               (QDC1)
```

The aligned formula for q14 becomes, in the total-frame coordinate,

```text
q_14(W)=(a W a W^*)^2=(a V h V^*)^2.                 (QDC2)
```

Therefore exact packet plus `q_19243` plus `q_14` is precisely the system

```text
X_e R Y_e=W                         (twelve edges e),
q_19243(W)=I_D,
(a W a W^*)^2=I_D,                                  (QDC3)
```

with the same cyclic-centralizer conditions on `X_e,Y_e` as before.

The last equation is itself a finite stratified double-coset condition.  Let

```text
C_a=U(rho(<t23>)')=U(D/2) x U(D/2),
n=D/2.
```

For each `0<=m<=n`, choose a unitary `S_m` such that the `-1` eigenspaces of
`a` and `S_m a S_m^*` have joint-sector dimensions

```text
(d_(--),d_(-+),d_(+-),d_(++))=(m,n-m,n-m,m).          (QDC4)
```

Then

```text
q_14(W)=I_D
 iff W in disjointUnion_(m=0)^n C_a S_m C_a.          (QDC5)
```

Thus q14 adds a thirteenth shifted-double-coset membership, stratified by one
integer, but it does **not** collapse a packet factorization gauge.  Every
independent transformation

```text
(X_e,Y_e)->(X_e Z_e,Z_e^(-1)Y_e),   Z_e in rho(A8)', (QDC6)
```

still fixes `W` and hence both collision equations.  The complete witness
fiber still contains `rho(A8)'^12`.

What q14 does supply is a direct gauge-invariant positive coordinate.  In the
total-frame notation set

```text
x_30(W)^2=1-Re tau(W a W^* h)
          =1-Re tau(V h V^* h).                       (QDC7)
```

The established q14 wall gives

```text
x_30(W)^2
 >=max(0,1/2-(1+sqrt(2))||q_14(W)-I||_2).             (QDC8)
```

In particular every exact point of `(QDC3)` has `x_30(W)^2>=1/2`, and the
constant is sharp before packet and 19243 are used.

The augmented system still has an exact finite-tracial escape.  Quotient
`A8*A8` by the thirty packet words, `q_19243`, and `q_14`.  All are true
kernel words, so the quotient maps to the binary-Leavitt target and its two
chart copies remain injective with trivial intersection.  In a finite factor
containing its group von Neumann algebra, the two regular finite-dimensional
chart algebras are unitarily conjugate.  That conjugator solves `(QDC3)`
exactly and necessarily lies on the positive side of `(QDC8)`.

Consequently q14 exposes the desired one-coordinate lower wall but cannot by
ordinary algebra force the opposing upper wall.  Any contradiction between
packet plus 19243 and `(QDC8)` remains a matrix/Connes-embedding-sensitive
statement.
