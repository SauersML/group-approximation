---
rg: 2
id: kt-no-denominator-window-balances-coefficient-and-canonical-inverse
kind: claim
title: No truncated denominator window balances Toeplitz repair with canonical amplification
artifacts:
  - research/kt-powered-cone-inverse-canonical-pairing-proof.md
distinct_from:
  kt-nilpotent-inverse-is-hs-cheap-only-before-canonical-amplification: That computes the one-step coefficient and full-additive errors; this treats every growing inverse depth, gives the exact powered kernel, and closes the near-full window left by the orbit calculation.
  kt-first-laurent-defect-has-exponentially-thin-gamma-orbit: That proves shallow and almost-full Gamma packets occupy zero site density; this proves moving to the remaining near-full depth makes the coefficient inverse itself maximally defective.
  kt-full-kazhdan-majorana-return-collapses-in-fd: That treats genuine finite-dimensional Laurent actors; this rules out one specific approximate truncated-cone architecture before exact actor collapse is available.
---

**ESTABLISHED TRUNCATED-CONE NO-GO; THE GLOBAL ROOT REMAINS OPEN.**

Let `X_N` be multiplication by `x_1` on

~~~text
V_N=T_N/P_N,
v_N=dim_F2(V_N),
~~~

and let `1<=M<=N`. The power `X_N^M` is a partial permutation with
kernel and cokernel dimension

~~~text
k_(N,M)
 =sum_(a=0)^(min(M-1,floor((N-1)/2)))
      (N-2a)(N-2a+1)/2.                                  (PWI1)
~~~

Consequently the optimal two-sided coefficient-Hilbert--Schmidt inverse
error is exactly

~~~text
sqrt(k_(N,M)/v_N).                                        (PWI2)
~~~

If `M_N/N->c<=1/2`, its square tends to
`1-(1-2c)^3`; for `c>=1/2` it is one. In particular,

~~~text
X_N^M=0                         for M>=ceil(N/2).          (PWI3)
~~~

Thus the near-full denominator window left open by the Gamma-orbit
saturation bound cannot approximate the Laurent inverse even on the small
coefficient carrier.

The shallow regime does not escape through canonical amplification. Put
`A_N=(V_N,+)` and let `C_(N,M)` be the composition matrix of
`a |-> X_N^M a` on `ell^2(A_N)`. Then

~~~text
rank C_(N,M)=2^(v_N-k_(N,M)),

inf_B max{||BC_(N,M)-I||_2,||C_(N,M)B-I||_2}
 =sqrt(1-2^(-k_(N,M))) ->1                                (PWI4)
~~~

uniformly for every `M>=1`. The same value is the optimal normalized
counting error of a set-theoretic two-sided inverse.

The named direction itself already has macroscopic canonical weight:

~~~text
eta_N=[y],             X_N^M eta_N=0.
~~~

Translation by `eta_N` pairs all `2^(v_N)` points of `A_N` into
equal-image pairs. Any candidate left inverse fixes at most one member of
each pair, so the named vector alone forces agreement at most `1/2` and
error at least `1/sqrt(2)`. The full kernel in (PWI1) strengthens this to
the asymptotically maximal error in (PWI4).

There is therefore no growth rate `M_N` for these cone truncations:

1. `M_N=o(N)` can make (PWI2) small, but (PWI4) tends to one.
2. Positive fractional depth gives a coefficient error floor.
3. Near-full depth has `X_N^M=0`.

Combined with the exact orbit size
`|Omega_N|=2^(8v_N)`, this closes both sides of the proposed growing-window
repair: shallow packets cannot spread the Laurent site, while packets deep
enough to approach the remaining orbit boundary destroy inverse covariance.
A future countermodel must abandon the canonical additive action of the
truncated multiplication map; changing only the window rate cannot work.

DERIVATION
kt-powered-cone-inverse-canonical-pairing-proof
