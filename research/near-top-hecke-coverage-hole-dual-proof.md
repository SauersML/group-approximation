---
rg: 2
id: near-top-hecke-coverage-hole-dual-proof
kind: route
title: Dualize the contractive Gram coverage of the near-top band
target: near-top-hecke-coverage-has-exact-hole-dual
requires:
  - almost-full-hecke-frame-gives-flexible-corner
  - regular-hecke-kraus-support-has-exact-order-dual
---

Fix `epsilon>0` and abbreviate

```text
L_epsilon=Q_epsilon L^2(D,tau).
```

On the finite Hilbert space `L_epsilon`, define the Gram-to-carrier map

```text
Psi_epsilon:B(L_epsilon) -> D,
Psi_epsilon(|A><C|)=C* A.                              (HCP1)
```

If `S>=0`, write `S=sum_j |A_j><A_j|` with
`A_j in L_epsilon`. Then

```text
Psi_epsilon(S)=sum_j A_j*A_j,
Tr_(L_epsilon)(S)=sum_j ||A_j||_2^2
                     =tau(Psi_epsilon(S)).             (HCP2)
```

Consequently (HCD1) is exactly the primal SDP

```text
c_epsilon=max {Tr(S): S>=0, Psi_epsilon(S)<=1}.        (HCP3)
```

Its feasible set is compact. Indeed, (HCP2) and
`Psi_epsilon(S)<=1` imply `Tr(S)<=tau(1)=1`. The
positive unit ball in a finite matrix algebra is compact, and all
constraints are closed. This also proves attainment and
`0<=c_epsilon<=1`.

Pair `D` with itself by `tau` and `B(L_epsilon)` by its ordinary trace.
For `Z=Z* in D`, the rank-one identity

```text
tau(Z Psi_epsilon(S))
 =Tr_(L_epsilon)(Q_epsilon R_Z Q_epsilon S)            (HCP4)
```

shows that

```text
Psi_epsilon*(Z)=Q_epsilon R_Z Q_epsilon.               (HCP5)
```

Dualizing the inequality `Psi_epsilon(S)<=1` introduces `Z>=0` and
gives

```text
min {tau(Z): Z>=0,
     Q_epsilon R_Z Q_epsilon>=Q_epsilon}.              (HCP6)
```

If `L_epsilon={0}`, both programs have value zero. Otherwise there is no
duality gap: `Z=c1` with `c>1` is strictly dual feasible, while a small
positive multiple of the identity on `L_epsilon` is strictly primal
feasible. Finite-dimensional SDP strong duality gives equality and
attainment. This proves (HCD2). Notice also that `Z=1` is feasible with
value one.

Let `S` attain (HCP3), decompose it as above, and set

```text
P=Psi_epsilon(S).
```

Then `P<=1` and

```text
tau(1-P)=1-c_epsilon.                                  (HCP7)
```

The almost-full near-top frame theorem applied to these `A_j` gives

```text
Delta^reg_(G,B)(X)
 <=sqrt(2 epsilon+4 tau(1-P))
 =sqrt(2 epsilon+4(1-c_epsilon)),                      (HCP8)
```

which is (HCD3). Statement (HCD4) follows immediately.

Finally suppose `Delta^reg_(G,B)(X)>=eta` and
`epsilon<=eta^2/4`. Squaring (HCP8) yields

```text
eta^2 <= 2 epsilon+4(1-c_epsilon),
1-c_epsilon >= (eta^2-2 epsilon)/4 >= eta^2/8.         (HCP9)
```

Let `Z` attain (HCP6). Then

```text
tau(Z)=c_epsilon<=1-eta^2/8,
```

and its feasibility is the second part of (HCD5). For
`A in L_epsilon`,

```text
<A,Q_epsilon R_Z Q_epsilon A>
 =tau(A* A Z)=tau(Z A*A).                              (HCP10)
```

Thus the compressed order inequality is equivalent to (HCD6), completing
the proof.
