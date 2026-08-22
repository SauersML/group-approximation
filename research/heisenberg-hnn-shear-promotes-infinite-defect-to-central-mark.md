---
rg: 2
id: heisenberg-hnn-shear-promotes-infinite-defect-to-central-mark
kind: claim
title: One HNN shear promotes any infinite-order defect to an infinite central mark
distinct_from:
  infinite-order-central-mark-group: that claim asks for the complete finitely presented Kazhdan compression group; this is the reusable algebraic operation applied after an infinite compression defect has already been constructed.
  power-pair-phase-hnn-has-finite-heisenberg-mark-models: that studies finite Heisenberg quotients of a power-pair cell; this is a torsion-free integral Heisenberg shear and proves survival by Britton embedding.
  linnell-skew-field-can-be-centrally-infinite: that obtains an infinite central scalar inside a skew field; this constructs an actual torsion-free finitely presented group with the central scalar in a prescribed normal closure.
---

Let `P` be a torsion-free finitely presented group and let `u in P` be
nontrivial.  Put

```text
B = P times <z>,
A = <u,z> <= B,
phi(u)=u z,   phi(z)=z,
H = HNN(B,A,phi).
```

Then:

1. `A ~= Z^2` and `phi` is an automorphism of `A`, so the displayed HNN
   extension is defined by the two relations

   ```text
   s u s^-1 = u z,      s z s^-1 = z.                 (HSH1)
   ```

2. `H` is torsion-free and finitely presented.
3. The base embedding `B -> H` is injective, so `z` has infinite order.
4. `z` is central in `H` and

   ```text
   z = (s u s^-1) u^-1 in <<u>>_H.                    (HSH2)
   ```

Thus any protected infinite-order compression defect can be promoted to a
nontrivial infinite-order **central** mark without imposing centrality as a
quotient relation.  The operation is a discrete integral-Heisenberg shear;
its survival and torsion-freeness are automatic consequences of the HNN
normal form rather than a lamp-orbit model.

The full proof is given by
`heisenberg-hnn-shear-promotes-infinite-defect-to-central-mark-proof`.
