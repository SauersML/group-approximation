---
rg: 2
id: kt-powered-cone-inverse-canonical-pairing-proof
kind: proof
title: Every powered cone inverse amplifies the named kernel direction to canonical mass
proves:
  - kt-no-denominator-window-balances-coefficient-and-canonical-inverse
requires:
  - kt-truncated-cone-inverse-rank-and-pointed-wall-proof
  - kt-congruence-stabilizer-traps-the-pointed-inverse-orbit-proof
---

# Every powered cone inverse amplifies the named kernel direction to canonical mass

## 1. The powered multiplication map

Retain

~~~text
V_N=T_N/P_N,
B_N={x_1^a y^b x_3^c:a+b+c<=N and a<b},
v_N=dim_F2(V_N),
X_N:V_N->V_N,        X_N[f]=[x_1f].
~~~

Declare the monomial basis `B_N` orthonormal over `C`. For
`1<=M<=N`, the power `X_N^M` is again a partial permutation. Its image
has basis

~~~text
{x_1^a y^b x_3^c in B_N:a>=M}.                            (1)
~~~

Indeed such a monomial has the unique preimage obtained by replacing
`a` by `a-M`. Conversely, multiplying an input by `x_1^M` either
lands at that basis vector, crosses into `P_N`, or passes the truncation
boundary.

Thus the kernel and cokernel have the common dimension

~~~text
k_(N,M)
 =sum_(a=0)^(min(M-1,floor((N-1)/2)))
      (N-2a)(N-2a+1)/2.                                   (2)
~~~

For fixed `a`, the summand in (2) counts `b>a` and `c>=0` with
`a+b+c<=N`. In particular,

~~~text
k_(N,1)=N(N+1)/2,
k_(N,M)=v_N                  if M>=ceil(N/2).              (3)
~~~

The second equality says that every near-full denominator window has
`X_N^M=0` already on the coefficient quotient.

## 2. Optimal coefficient-HS inverse error

For every matrix `Y`, the restriction of `YX_N^M-I` to the kernel is
minus the identity. The range of `X_N^MY` is contained in the range of
`X_N^M`, so its distance from the identity has the same cokernel lower
bound. Hence

~~~text
max{||YX_N^M-I||_(2,v_N),||X_N^MY-I||_(2,v_N)}
 >=sqrt(k_(N,M)/v_N).                                      (4)
~~~

Equality is attained. Invert `X_N^M` on its initial space and extend
that inverse by a unitary from the cokernel to the kernel. The two products
are then the initial and final support projections. Therefore

~~~text
inf_(Y unitary) max{||YX_N^M-I||_2,||X_N^MY-I||_2}
 =sqrt(k_(N,M)/v_N).                                       (5)
~~~

If `M_N/N->c` with `0<=c<=1/2`, summing (2) gives

~~~text
k_(N,M_N)/v_N -> 1-(1-2c)^3.                              (6)
~~~

For `c>=1/2` the ratio is one by (3). Thus coefficient-HS repair is
cheap only in the shallow regime `M_N=o(N)`. At every fixed positive
fraction of the truncation depth it already has a positive defect floor,
and throughout the near-full window its defect is exactly one.

## 3. Canonical additive amplification

Now retain the additive root carrier

~~~text
A_N=(V_N,+),                 |A_N|=2^(v_N),
mathcal X_(N,M)(a)=X_N^M(a).
~~~

Let `C_(N,M)` be its composition matrix on `ell^2(A_N)`:

~~~text
C_(N,M) delta_a=delta_(mathcal X_(N,M)(a)).
~~~

The linear map `mathcal X_(N,M)` has a kernel of size
`2^(k_(N,M))` and an image of size `2^(v_N-k_(N,M))`. Therefore

~~~text
rank C_(N,M)=2^(v_N-k_(N,M)).                              (7)
~~~

For any matrix `B`, both `BC_(N,M)` and `C_(N,M)B` have rank at most
the number in (7). The normalized Hilbert--Schmidt distance from the
identity to rank at most `r` is at least `sqrt(1-r/2^v_N)`.
The Moore--Penrose inverse attains both bounds. Consequently

~~~text
inf_B max{||BC_(N,M)-I||_2,||C_(N,M)B-I||_2}
 =sqrt(1-2^(-k_(N,M))).                                    (8)
~~~

The same statement holds for set-theoretic permutation repair. For every
map `Y:A_N->A_N`, the equation

~~~text
Y(mathcal X_(N,M)(a))=a
~~~

can hold for at most one point in each kernel coset. Hence its agreement
fraction is at most `2^(-k_(N,M))`, and the optimal normalized counting
error is the right side of (8).

Since `k_(N,M)>=k_(N,1)=N(N+1)/2` for every `M>=1`,

~~~text
sqrt(1-2^(-k_(N,M))) ->1                                  (9)
~~~

uniformly over every nonzero denominator window.

## 4. The named vector alone already has half the mass

Let

~~~text
eta_N=[y] in V_N.
~~~

It satisfies `X_N eta_N=[x_1y]=[x_2]=0`, and hence
`X_N^M eta_N=0` for every `M>=1`. Translation by `eta_N` partitions
`A_N` into exactly `2^(v_N-1)` disjoint pairs

~~~text
{a,a+eta_N}.
~~~

The two members of each pair have the same image under
`mathcal X_(N,M)`. A candidate left inverse can therefore fix at most one
member of each pair. Even if every other kernel direction is discarded,
the named direction by itself gives

~~~text
agreement fraction <=1/2,
normalized counting inverse error >=1/sqrt(2).             (10)
~~~

Thus the pointed coefficient defect does not become a rank-one event after
canonical amplification. It is copied across half of the canonical additive
carrier. The full kernel subgroup upgrades the half-mass bound (10) to the
asymptotically maximal bound (9).

## 5. No denominator-window balance

Equations (5) and (8) leave no scale to tune:

1. If `M_N=o(N)`, the coefficient-HS inverse may be cheap, but the
   canonical additive inverse defect tends uniformly to one.
2. If `liminf M_N/N>0`, the coefficient-HS inverse already has a positive
   floor from (6).
3. If `M_N>=ceil(N/2)`, which includes the near-full orbit window left by
   the congruence-saturation theorem, `X_N^M=0` and both inverse defects
   equal one.

Therefore the near-full denominator-depth window cannot extend the
truncated-cone construction across a Laurent inverse while retaining the
canonical root carrier. The exact `|Omega_N|=2^(8v_N)` orbit calculation
shows that shallow packets cannot spread the site; the powered inverse
calculation here shows that moving the packet to the only remaining
near-full depth destroys the actor relation before any Clifford or lamp
rounding begins.

This is a terminal no-go for the truncated-cone/Toeplitz architecture, not
for arbitrary noncongruence matrix microstates. A different construction
would have to abandon the canonical additive action of `X_N`, rather than
choose a more clever growth rate for the same truncations. The global
nonhyperlinearity root remains open.
