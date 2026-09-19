---
rg: 2
id: titz-witzel-c2-cocycle-system
kind: claim
title: The C2-block route to the Titz--Witzel gate is an explicit two-permutation nonabelian cocycle system
distinct_from:
  titz-witzel-two-generator-involution-sandwich-normal-form: That rewrites the abstract two-generator presentation; this evaluates every derived word and relator after imposing the exact C2 block quotient and exposes the two fibre permutations and their ordered cocycle equations.
  titz-witzel-central-square-lifts-collapse-mark: That excludes central-square lifts metrically; this gives the full nonabelian block system, its exact defect formulae, and an approximate-conjugacy consequence of the square-root equation.
artifacts:
  - research/artifacts/titz-witzel-c2-block-cocycle-check.py
---

**THEOREM.**  Let `X` be a finite set and put `Omega=X times C2`.  Use the
imprimitive-wreath notation

```text
[A0,A1]_epsilon (x,i)=(A_(i+epsilon) x,i+epsilon),
[A]_epsilon [B]_delta
  =[A0 B_epsilon,A1 B_(1+epsilon)]_(epsilon+delta),       (TWC1)
```

where all subscripts are modulo two and products of permutations are composed
from right to left.  Normalize the exact block-swapping involution and write

```text
e=[1,1]_1,                         u=[P,Q]_1.              (TWC2)
```

Define the following ordered words in `P,Q`:

```text
H0=P Q^(-1),                 H1=Q P^(-1),
A0=H1,                       A1=H0,
V0=P Q,                      V1=Q P,
X0=A0 V1,                    X1=A1 V0,
C0=V0 A0 V1,                C1=V1 A1 V0,
F0=X1^(-1) H1 X0,           F1=X0^(-1) H0 X1,
D0=A0^(-1) F0,              D1=A1^(-1) F1,
S0=F0 A1 F0,                S1=F1 A0 F1,
R0=X1^(-1) S0^(-1) C1^(-1),
R1=X0^(-1) S1^(-1) C0^(-1),
B0=R0 R1^(-1),              B1=R1 R0^(-1),
T0=B0 A1,                    T1=B1 A0.                    (TWC3)
```

For the derived words in `(TW2G1)` and `(TWIS1)`, one then has

```text
h=[H0,H1]_1,   a=[A0,A1]_1,   x=[X0,X1]_1,
c=[C0,C1]_1,   f=[F0,F1]_1,   d=[D0,D1]_1,
s=[S0,S1]_1,   rho=[R0,R1]_1,
beta=[B0,B1]_1,              p=[T0,T1]_0.                 (TWC4)
```

Consequently the four approximate relators in the involution-sandwich gate
evaluate exactly as

```text
c^2                 =[C0 C1,             C1 C0]_0,
rho^2 e u^(-1)      =[R0 R1 P^(-1),      R1 R0 Q^(-1)]_0,
beta a u d^(-1)     =[T0 P D0^(-1),      T1 Q D1^(-1)]_0,
p u p c             =[T0 P T1 C1,        T1 Q T0 C0]_0,  (TWC5)
```

while

```text
u^8=[(P Q)^4,(Q P)^4]_0.                                  (TWC6)
```

Thus an exact block solution is precisely the ordered finite-group system

```text
C1=C0^(-1),
P=R0 R1,                    Q=R1 R0,
D0=T0 P,                    D1=T1 Q,
C0=T0 P T1,                 C1=T1 Q T0.                  (TWC7)
```

No commutation is licensed in `(TWC3)--(TWC7)`.  In particular the
square-root equation forces `P` and `Q` to be conjugate in every exact
solution.  Quantitatively, if `delta_0` is the normalized Hamming defect of
`rho^2 e u^(-1)`, then

```text
d_X(Q,R0^(-1) P R0) <= 2 delta_0.                         (TWC8)
```

Let `delta_c` be the defect of `c^2` and let
`mu=d_Omega(u^8,1)`.  The block formulae sharpen the two existing
noncommutation requirements to

```text
mu=d_X((P Q)^4,1),
mu <= delta_c+6 d_X(P,Q),
mu <= delta_c+6 d_X(P Q,Q P).                            (TWC9)
```

Hence any positive C2-block construction needs both `P` versus `Q` and
`P Q` versus `Q P` to disagree on positive density.  This is an exact
normal form and a necessary-condition theorem; it does not construct the
required approximate models.

---

### Proof

titz-witzel-c2-cocycle-system-proof
