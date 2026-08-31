---
rg: 2
id: kt-finite-ring-specializations-kill-the-named-laurent-return
kind: claim
title: Every finite-ring Kun--Thom specialization kills the named Laurent return
artifacts:
  - research/finite-unit-inverses-collapse-the-kt-positive-core-proof.md
distinct_from:
  kt-steinberg-deleted-line-embeddings-have-scalar-commutants: That constructs one regular-character congruence tower and proves scalar commutants after a one-line compression; this applies to every finite target ring before choosing a representation and identifies why the Laurent return disappears algebraically.
  kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence: That proves the return has a maximal exact Fourier wall in the infinite tracial wreath; this proves no finite-ring specialization can retain it.
---

**ESTABLISHED CONGRUENCE NO-GO; ARBITRARY MATRIX MICROSTATES REMAIN.**

Let

~~~text
R_+=F_q[x_1,x_2,x_3],
R=F_q[x_1^(+-1),x_2^(+-1),x_3^(+-1)].
~~~

For every unital homomorphism `theta:R->T` to a finite unital ring,

~~~text
theta(R_+)=theta(R).                                     (KFR1)
~~~

Consequently

~~~text
theta(EL_r(R_+))=theta(EL_r(R)).                         (KFR2)
~~~

In particular the fixed Laurent return

~~~text
h=e_12(x_1^(-1)x_2)
~~~

has image in the image of `Gamma=EL_r(R_+)`. Any matrix commuting with
the specialized `Gamma` therefore commutes with the specialized `h`
exactly.

Thus no finite-ring quotient, finite-field evaluation, or representation
factoring through such a congruence quotient can realize the cyclic parity
leak. Exhaustive small-quotient experiments in this class are guaranteed to
return zero and cannot find a countermodel.

The proof uses only finiteness: each `theta(x_i)` is a unit of the finite
ring and hence has finite multiplicative order, so its inverse is a positive
power already in `theta(R_+)`. The obstruction is therefore not a missing
choice of congruence level. A leaking matrix model would have to be
genuinely noncongruence and everywhere inexact on the actor/multiplicity
sector. The global root remains **OPEN**.

DERIVATION
finite-unit-inverses-collapse-the-kt-positive-core-proof
