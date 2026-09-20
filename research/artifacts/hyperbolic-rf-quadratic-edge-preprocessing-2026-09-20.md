# Quadratic padding for cyclic-edge matching

Date: 2026-09-20. A quantitative improvement to the existing triangle
preprocessing, with a complete finite-dimensional proof. This does not
settle one-edge holonomy absorption or hyperbolic residual finiteness.
No novelty is claimed for the standard spectral-overlap and polar tools.

## 1. Spectral transport pays the square of the error

Use unnormalized trace Tr and ||A||_(2,d)^2=Tr(A*A)/d.
Let U^p=V^p=I, zeta=exp(2 pi i/p), and write

```
U=sum_k zeta^k P_k,  V=sum_l zeta^l Q_l,
a_kl=Tr(P_k Q_l)>=0,  s_p=2 sin(pi/p).
```

The nonnegative matrix a has row sums r_k=rank P_k and column sums
s_k=rank Q_k. Expanding Tr((U-V)*(U-V)) gives the EXACT identity

```
d ||U-V||_(2,d)^2 = sum_(k,l) |zeta^k-zeta^l|^2 a_kl.
```

Consequently its off-diagonal mass E satisfies

```
E=sum_(k!=l) a_kl <= d ||U-V||_(2,d)^2/s_p^2.
```

For each k, r_k-s_k=sum_(l!=k)(a_kl-a_lk), so |r_k-s_k|<=E.
In fact (1/2) sum_k |r_k-s_k|<=E, by viewing a as a transport
coupling. These are integer multiplicity differences, not normalized
traces. This is stronger than applying Cauchy--Schwarz to tr(P_k-Q_k),
which loses a square root.

## 2. Equal multiplicities give a linear near-identity intertwiner

Suppose r_k=s_k for every k. Put T=sum_k P_k Q_k. Then UT=TV,
T*T=sum_k Q_k P_k Q_k commutes with V, and

```
Tr T=Tr(T*T)=sum_k a_kk,
||T-I||_(2,d)^2=E/d <= ||U-V||_(2,d)^2/s_p^2.
```

The polar partial isometry of T intertwines V and U on its initial
and final supports. Those supports have the same eigenvalue counts
for each k; subtracting from r_k=s_k shows that ker T and ker T*
also have matching counts. Complete the polar part by an arbitrary
unitary intertwiner on these kernels, obtaining a unitary w with
wVw*=U.

Every such completion is a nearest unitary to T in HS norm: for the
singular values sigma_j of T,

```
||w-T||_HS^2=sum_j (1-sigma_j)^2 <= ||I-T||_HS^2.
```

For completeness, the inequality follows from
sum_j sigma_j >= Re Tr T and expansion of both squared norms; the
completed polar factor realizes sum_j sigma_j in Re Tr(w*T).
Therefore

```
||w-I||_(2,d) <= 2 ||T-I||_(2,d) <= 2 ||U-V||_(2,d)/s_p.
```

No dimension, irreducibility, or lower bound on individual spectral
multiplicities enters this estimate.

## 3. Pad the triangle by O(epsilon^2 d) linear characters

Vertex groups X_0=<a,b>, X_1=<c,b>, X_2=<c,a> have the split
abelianizations in the claim. Use integer multiplicity vectors and put

```
delta_b=r(rho_0(b))-r(rho_1(b)),
delta_a=r(rho_0(a))-r(rho_2(a)),
delta_c=r(rho_1(c))-r(rho_2(c)),
M=max_(e,k) |delta_e(k)|.
```

All deltas sum to zero, and Section 1 gives M<=d epsilon^2/s_p^2.
If M=0, use no padding. Otherwise set u=(M,...,M) and m=pM.
Prescribe the edge multiplicities of the extra representations S_i:

| Vertex | First marginal | Second marginal |
|---|---|---|
| X_0 | a: u | b: u |
| X_1 | c: u | b: u+delta_b |
| X_2 | c: u+delta_c | a: u+delta_a |

Each pair consists of nonnegative integer vectors of total m. A
nonnegative integer transport matrix with these two marginals exists:
successively allocate the minimum remaining row and column demand.
Each entry is realized by that many copies of the corresponding
linear character of (Z/p)^2. For X_0 one can use the DIAGONAL matrix
with entries M, so no divisibility assumption or rounding of M is
needed. The S_i are genuine representations of their vertex groups.

The padded rho_i^+=rho_i direct_sum S_i all have dimension D=d+m
and agree in spectral multiplicities on every edge. On the extra
block every difference of unitaries has squared HS norm at most 4m.
Thus each padded edge error is bounded by

```
eta=sqrt((d epsilon^2+4m)/(d+m))
    <= sqrt(1+4p/s_p^2) epsilon,
m/d <= p epsilon^2/s_p^2.
```

## 4. Align a and b, retaining linear error on c

Apply Section 2 to rho_0^+(b),rho_1^+(b), obtaining w_1 with
||w_1-I||_(2,D)<=2 eta/s_p. Independently apply it to the a-edge,
obtaining w_2 with the same bound. Set

```
rho_0'=rho_0^+,
rho_1'=Ad(w_1) rho_1^+,
rho_2'=Ad(w_2) rho_2^+.
```

The b- and a-edges now agree exactly. For every unitary A,
||wAw*-A||_2<=2||w-I||_2. Hence the c-edge error is at most

```
eta+2||w_1-I||_2+2||w_2-I||_2
 <= (1+8/s_p) eta.
```

All vertex relations are retained exactly. The original d-coordinate
compression of rho_i^+ is rho_i, and HS error after this compression
is at most sqrt(D/d) times the ambient normalized error. Thus the
preprocessing loses no square root as epsilon->0.

## 5. Scope and sharpness of the padding order

Take U=I_d and V diagonal with k entries zeta and d-k entries 1.
Then epsilon^2=s_p^2 k/d and the rank discrepancy is k. Any additive
spectral compensation making the two original spectra agree must
add at least k dimensions on the deficient side. Therefore a general
o(epsilon^2 d) compensation bound is impossible. This statement is
about additive compensation of given representations; arbitrary
changes of the original representations are not covered by this
lower bound.

For p=7 the bounds above are absolute constants. This improves the
quantitative input to the GHB_2(7) one-edge problem but supplies no
operation that removes the final c mismatch while retaining the
other two edges. That simultaneous step is still open. In particular
linear preprocessing is not a linear stability theorem.
