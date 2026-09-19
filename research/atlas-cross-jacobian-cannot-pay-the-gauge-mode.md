---
rg: 2
id: atlas-cross-jacobian-cannot-pay-the-gauge-mode
kind: claim
title: A nonlinear--linear Atlas cross-Jacobian cannot pay the scalar gauge mode
distinct_from:
  atlas-phase-jacobian-has-invertible-gauge-kernel: that treats the nonlinear holonomy Jacobian alone; this permits coupling it to the additive-row Jacobian and proves that every cross term still vanishes on the gauge direction.
  atlas-one-functional-gauge-pin-cannot-create-shrinkage: that treats a coordinate slice selected by one functional; this treats bilinear Gauss--Newton and cross-Hessian attempts without selecting a slice.
  atlas-five-row-operator-phase-lift: that is the desired nonlinear-to-linear energy inequality; this proves that charging the gauge direction with an additive-Jacobian diagonal block already requires the left-side energy and is therefore circular.
---

**ESTABLISHED FIREWALL.**  Let `F(U)` be the six nonlinear Atlas phase
holonomies (with identity targets subtracted if desired), and let `L(U)` be
the five additive circulations.  Their differentials at every relative
unitary satisfy

```text
J_F(U)[iU]=0,
J_L(U)[iU]=iL(U).                                     (CJG1)
```

The first identity is scalar invariance; the second is scalar equivariance.

Consequently every bilinear cross-Jacobian term

```text
<J_F(U)[T], B J_L(U)[T]>
```

vanishes at `T=iU`, for every coefficient operator `B`.  Adding its adjoint
does not change this.  Thus cross terms cannot remove the invertible gauge
kernel of the nonlinear Jacobian.

More generally, let a positive Gauss--Newton form be built from the combined
Jacobian:

```text
Q_U(T)=< (J_F[T],J_L[T]),
          M (J_F[T],J_L[T])>,          M>=0.           (CJG2)
```

Writing `M_LL` for its additive--additive block, `(CJG1)` gives exactly

```text
Q_U(iU)=<iL(U),M_LL iL(U)>.                            (CJG3)
```

If `M_LL=0`, positivity forces both cross blocks to be zero, so `(CJG2)` is
just a nonlinear-Jacobian form and retains the invertible zero mode.  If
`M_LL!=0`, the only payment on that mode is a quadratic expression in the
additive circulation itself.  Bounding it by nonlinear defect is already a
form of the missing five-row estimate; the cross-Jacobian has not derived
that estimate.

Therefore neither a bilinear Hessian between nonlinear and additive rows nor
a positive combined Gauss--Newton form supplies an independent gauge-pinned
shrunk-space invariant.  A successful mixed singular-space construction
must introduce an authenticated operator not annihilated by scalar gauge and
whose energy is controlled by the existing nonlinear relators without using
`||L(U)||_2` as an input.
