---
rg: 2
id: kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence
kind: claim
title: The cyclic parity is an exact quasi-regular return correspondence
artifacts:
  - research/kt-parity-fourier-orbit-and-conditional-expectation-proof.md
distinct_from:
  kt-order-three-average-does-not-kill-the-pointed-martingale-wall: That proves a fixed commutator and a lower bound on distance from the backward range; this identifies the entire orbit correspondence and computes the conditional expectation and distance exactly.
  kt-regular-congruence-mask-removes-trace-faithfulness-from-the-commutant-wall: That embeds an arbitrary pre-existing multiplicity vector behind a regular character; this identifies the precise quasi-regular pointed representation which such a vector must realize.
---

**ESTABLISHED EXACT FOURIER CALCULATION; THE MATRIX GATE REMAINS OPEN.**

Keep the pinned Kun--Thom notation and put

~~~text
H=B^(-1) Gamma B,
P={Gamma,C^(-1)Gamma,C^(-2)Gamma} subset G/Gamma,
v=product_(x in P) z_x,
q=(1+v)/2.
~~~

In the canonical binary wreath von Neumann algebra `M=L(W)`, let

~~~text
R=sigma(Gamma)' intersect M,
S=Phi_B(R)=sigma(H)' intersect M.
~~~

Then the stabilizer of the three-site set `P` inside `H` is exactly
`Gamma`. Consequently the closed span

~~~text
K=closure span { sigma(k) v sigma(k)^* : k in H }
~~~

has the orthonormal basis `{z_(kP):kGamma in H/Gamma}`, and conjugation
by `H` on `K` is exactly the quasi-regular representation

~~~text
lambda_(H/Gamma).                                        (KQR1)
~~~

The index `[H:Gamma]` is infinite. Hence `K` has no nonzero
`H`-fixed vector. If `E_S:M->S` is the trace-preserving conditional
expectation, then

~~~text
E_S(v)=0,
E_S(q)=1/2,
dist_2(q,S)=1/2.                                         (KQR2)
~~~

Thus the earlier `1/(2 sqrt(2))` commutator estimate is not sharp: the
cyclic parity is a full martingale difference of norm `1/2`.

This is the exact pointed content of the remaining matrix problem. A
hyperlinear model retaining the wall must realize a copy of the
quasi-regular `H/Gamma` correspondence in an adjoint matrix ultraproduct
with its root basis vector represented by the operator-norm-one involutions
`v_n`. Conversely, a proof of non-hyperlinearity must show that the full
`C`-compatible actor equations exclude precisely this pointed
quasi-regular correspondence. Adjoint spectral-rank estimates do not see one
such bounded vector.

No dimension-free algebraic sum-of-squares identity derived only from the
group and lamp relations can force this vector to vanish: the exact tracial
model above satisfies every relation and has (KQR2). Any successful
separation must distinguish matrix-embeddable traces from this exact trace,
rather than use tracial positivity alone. The global root remains **OPEN**.

DERIVATION
kt-parity-fourier-orbit-and-conditional-expectation-proof
