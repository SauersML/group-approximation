---
rg: 2
id: kt-intermediate-actor-cannot-extract-positive-coefficient-transport
kind: claim
title: Intermediate KT actor relations cannot extract positive coefficient-transport support
artifacts:
  - research/kt-finite-steinberg-packets-have-shrinking-transport-proof.md
distinct_from:
  kt-canonical-lamp-collision-forces-vanishing-intertwiner: That proves any infinite-fiber transport in an arbitrary canonical microstate has vanishing support; this constructs exact coherent finite models attaining the optimal shrinking support on every finite packet.
  kt-single-laurent-return-has-profinite-coset-models: That constructs exact canonical models retaining the named return wall; this adds the optimal partial transports and turns those models into an actor-to-carrier extraction no-go.
  kt-full-kazhdan-majorana-return-collapses-in-fd: That uses genuine representations of the full Laurent actor; this identifies why relations of the smaller intermediate actor cannot supply the large-support passage to that collapse.
---

**ESTABLISHED EXTRACTION FIREWALL; FULL-LAURENT EXTRACTION REMAINS OPEN.**

Let

~~~text
H=<Gamma,e_12(y)>=EL_3(F_2[x_1,y,x_3])
~~~

and let `W_H` be its coherent binary wreath over `H/Gamma`. The finite
truncation quotients give exact finite-dimensional representations of all
`H` actor and Steinberg relations whose characters converge to the
canonical character of `W_H`.

For any `r>=1`, choose the fixed coefficient-kernel sites

~~~text
eta_0=0,
eta_j=[x_1^(j-1)y^j],             1<=j<=r,
X eta_j=0.
~~~

At every sufficiently deep truncation these are distinct. If `z_j` are
their lamp involutions and `w=z_0`, the projection

~~~text
T_r=E_r=2^(-r) product_(j=1)^r(I+z_0z_j)                  (IES1)
~~~

satisfies

~~~text
wT_r=T_rz_j                    for 0<=j<=r,
tr(T_r^*T_r)=2^(-r).                                    (IES2)
~~~

This support is optimal: the canonical collision Fourier estimate forces

~~~text
tr(T^*T)<=2^(-r)                                          (IES3)
~~~

for every partial isometry satisfying the same rows. Taking `r->infinity`
slowly produces exact canonical finite models in which every fixed
coefficient-transport row eventually holds, but the transport support tends
to zero.

Consequently there is no theorem whose hypotheses are only canonical trace
plus the relations of the intermediate actor `H` and whose conclusion
extracts one partial transport with both:

~~~text
liminf tr(T_n^*T_n)>0,
||w_[Xg],n T_n-T_nz_[g],n||_2->0 for every fixed [g].
~~~

The obstruction is not a bad choice of polar factor: the upper bound (IES3)
matches the explicit construction (IES1).

This is the finite-packet escape left by the arbitrary-microstate collision
theorem. Any positive actor-to-carrier extraction must use relations absent
from `H`: a genuinely full Laurent inverse direction, or simultaneous
external Kun--Thom compressor compatibility. The exact mathematical target
is now narrow: prove that those extra relations prevent support from
shrinking as `2^(-r)`. Intermediate Steinberg coherence alone provably
cannot.

DERIVATION
kt-finite-steinberg-packets-have-shrinking-transport-proof
