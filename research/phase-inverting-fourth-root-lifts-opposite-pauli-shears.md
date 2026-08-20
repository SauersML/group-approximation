---
rg: 2
id: phase-inverting-fourth-root-lifts-opposite-pauli-shears
kind: claim
title: A central fourth root lifts both opposite Pauli shears as involutions
artifacts:
  - experiments/phase_corrected_pauli_shears.py
distinct_from:
  six-generator-fixed-kernel-rank-jump-admits-opposite-shears: that concerns preservation of a two-dimensional alternating-form pencil over a polynomial ring; this repairs the quadratic refinement already on one Pauli plane.
  cyclic-phase-pauli-shears-have-unbounded-clock-order: that tensors this correction over cyclic polynomial Frobenius spaces and proves unbounded clock order; this is the atomic order-six lift.
---

Let

```text
P=<R,p,q | R^4=p^2=q^2=1, [R,p]=[R,q]=1, [p,q]=R^2>.          (PIS1)
```

Then `|P|=16`, and the assignments

```text
alpha: R|->R^-1, p|->p,     q|->R p q,
beta:  R|->R^-1, p|->R p q, q|->q                              (PIS2)
```

extend to automorphisms satisfying

```text
alpha^2=beta^2=1,                 (alpha beta)^3=1.             (PIS3)
```

Their actions on `P/<R> ~= F_2^2` are the two opposite transvections.  The
inversion of `R` is essential: if `R` is fixed, applying either nominal shear
twice multiplies the sheared generator by `R^2`, so its lift has order four.

Thus the alternating-form opposite-shear clock is compatible with the Pauli
quadratic refinement after one bounded phase enlargement.  This does not by
itself make the resulting polynomial phase-Pauli module finitely presented.
