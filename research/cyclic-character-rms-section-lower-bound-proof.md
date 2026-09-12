---
rg: 2
id: cyclic-character-rms-section-lower-bound-proof
kind: route
title: Induce the r-exponent character and compare its phase gap with cell charge
target: cyclic-core-character-forces-linear-rms-section-area
requires:
  - bounded-period-iwahori-quotients-are-finite
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - induced-rounding-needs-rms-section-fillings
---

The order calculation in `(CCA3)` proves that `theta_K` is a genuine
character of the finite core image.  Frobenius reciprocity gives

```text
Hom_(A_N)(1,Ind_(B_N)^(A_N)(theta_K))
 =Hom_(B_N)(1,theta_K)=0.                              (CCP1)
```

Let `q=[A_N:B_N]`.  In the section basis, the induced action is a monomial
matrix whose edge phase is `theta_K(b_(t,a))`, where `b_(t,a)` is the
Schreier transition.  Multiplying the constant vector on the `q` cosets by
the phases of the chosen section words is a gauge change.  Its displacement
under a generator is exactly

```text
q^(-1) sum_t |zeta^(Phi(ell_(t,a)))-1|^2,             (CCP2)
```

where `Phi` is `r`-exponent modulo `K` and `ell_(t,a)` is the section edge
loop.  The uniform finite-quotient spectral gap and `(CCP1)` bound the
generator average in `(CCP2)` below by `kappa`.

In a relative van Kampen expression for `ell_(t,a)`, conjugation does not
change `Phi`, exact-core cells have charge zero, and each charged endpoint
cell contributes `2` or `3` modulo `K` by `(CCA4)`.  The chordal triangle
inequality proves `(CCA5)`.  Hence

```text
max_a 1/q sum_t Area(ell_(t,a))^2
 >= kappa K^2/(36 pi^2 |S|),                          (CCP3)
```

up to the convention of whether the Cayley gap is a maximum or generator
average.  Taking square roots proves `(CCA2)`.

For the regularized last assertion, twisting the regular representation of
`B_N` by `theta_K` leaves its isomorphism class unchanged.  Thus the twisted
core is the literal restriction of a conjugate exact regular endpoint.
Keeping the untwisted endpoint involution instead creates only the scalar
residuals `zeta^2-1` and `zeta^3-1`.  Its fixed word traces still converge
to the canonical character, while replacing `zeta rho(r)` by `rho(r)` is
an explicit `O(1/K)` exact repair.  The same scalar phases occur in every
induced fiber, so `(CCP2)` retains its fixed lower bound.

