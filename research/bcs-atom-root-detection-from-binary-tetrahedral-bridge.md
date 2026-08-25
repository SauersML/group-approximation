---
rg: 2
id: bcs-atom-root-detection-from-binary-tetrahedral-bridge
kind: route
title: Put every source root in a shared negative-center binary-tetrahedral packet
target: canonical-bcs-root-detection-via-binary-tetrahedral-bridge
requires:
  - odd-characteristic-adaptive-tree-wordization
  - binary-tetrahedral-conditional-e5-root-bridge
---

Choose characteristic three in the finite base-change compiler.  For a
source `a_(sigma,i)=q_sigma P_i`, let `H_i` be the finite two-group whose
character idempotent on the old negative central sector is `P_i`.  The
coefficient identities `h a_(sigma,i)=a_(sigma,i) h=a_(sigma,i)` for
`h in H_i` make `Z_(sigma,i)=x_13(a_(sigma,i))` commute with `H_i`; the
elementary-matrix model keeps this exact order-three root nontrivial.

The characteristic-three choice introduces no denominator conflict.  The
BCS assignment projections, Pauli seed, and optional extraspecial role
packet use only two-primary denominators.  The binary-tetrahedral group is
an external ordinary finite group and is not encoded by coefficients of the
base-change ring.  Hence the integer `D` in the base-change theorem is prime
to three; pass to a finite extension of `F_3` only to split the fixed
two-primary packet tables.

Apply `(BTB2)` to every member of the fixed finite menu, sharing one fresh
central involution `ell`.  Bass--Serre normal form preserves the wordized
base and all attached packet factors.  On the common negative `ell` sector,
any carrier reducing the packets satisfies `(BTB4)` with
`E=Q_sigma P_i`.  Fixed finite-group correction and the amalgam relator
`y_(sigma,i)=Z_(sigma,i)` give the robust estimate `(BZR2)` with
`c_root=1/2`.

The perfect model sends every source root to one, sends `ell` and all
binary-tetrahedral factors to one, and retains the old marked BCS action.
The restrictions on every amalgamated subgroup agree, so all the finite
attachments extend simultaneously.
