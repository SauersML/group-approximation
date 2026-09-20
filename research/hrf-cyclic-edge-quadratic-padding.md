---
rg: 2
id: hrf-cyclic-edge-quadratic-padding
kind: claim
title: Cyclic-edge spectral transport gives quadratic padding and linear-error preprocessing for triangle matching
distinct_from:
  triangle-edge-matching-reduces-to-one-edge-holonomy: that establishes the qualitative equivalence and now consumes this lemma; this supplies the explicit quadratic padding and linear error estimates by spectral overlap transport.
artifacts:
  - research/artifacts/hyperbolic-rf-quadratic-edge-preprocessing-2026-09-20.md
---

Let p>=2, s_p=2 sin(pi/p), and consider a triangle of finite groups
whose cyclic order-p edge generators form a basis of each vertex
abelianization (Z/p)^2. Let rho_0,rho_1,rho_2 be genuine unitary
representations in the SAME dimension d, with normalized HS error at
most epsilon on each common edge a,b,c.

There are linear-character sums S_i, all of one common dimension m, and
unitaries w_1,w_2 in dimension D=d+m, with w_0=I, such that

```
m <= p epsilon^2 d / s_p^2,
rho_i' = w_i (rho_i direct_sum S_i) w_i*,
rho_0'(b)=rho_1'(b),  rho_0'(a)=rho_2'(a),
||rho_1'(c)-rho_2'(c)||_(2,D)
   <= (1+8/s_p) sqrt(1+4p/s_p^2) epsilon,
||w_i-I||_(2,D) <= (2/s_p) sqrt(1+4p/s_p^2) epsilon.
```

Every padded vertex representation remains genuine. Relative to its
padded input, conjugation changes each vertex-group element by at most
twice the displayed bound on w_i-I. Compressing back to the original
d coordinates costs at most sqrt(D/d), which tends to one as epsilon
tends to zero. If the three edge spectra already have equal
multiplicities, m=0 suffices.

The basic spectral fact is that order-p unitaries U,V satisfy

```
max_k |rank P_k(U)-rank P_k(V)| <= d ||U-V||_2^2 / s_p^2.
```

For equal multiplicities they admit an exact intertwining unitary w
with ||w-I||_2 <= 2 ||U-V||_2/s_p. The padding's quadratic order in
epsilon is sharp for spectral compensation in general, already for
one eigenvalue mismatch.

For GHB_2(7) this improves preparation of the one-edge problem; it does
NOT solve its remaining simultaneous matching problem, prove flexible
HS stability, or decide hyperbolic residual finiteness.

## Proof status

Direct finite-dimensional proof in the linked artifact. No asymptotic
stability, Liu internality, or property (T) is assumed. No novelty claim
is made for the spectral transport or polar-decomposition ingredients.

Independent review on 2026-09-20 checked the spectral identity, polar
completion, transport signs, constants, and compression normalization.
