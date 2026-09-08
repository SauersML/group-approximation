---
rg: 2
id: bffhz-computable-core-fp-upgrade-is-false
kind: claim
title: A decidable simple MIF core refutes the universal computable-core finite-presentation upgrade of the BFFHZ action
invalidates: [bffhz-action-image-is-finitely-presented]
artifacts:
  - research/artifacts/boone-higman-relative-automorphism-fp-obstruction-2026-09-08.md
---

For the regular cyclic twisted group T=Z V_Z of
`regular-cyclic-twisted-core-is-decidable-mif-non-fp`, and every finite
n>=2, put A=Aut_T(T*F_n) and let K be the kernel of its action on
Hom_T(T*F_n,T). Then

    K=1,                 A/K is not finitely presented.

T is infinite, finitely generated, computably presented and simple, so
this is a counterexample to `bffhz-action-image-is-finitely-presented`
exactly as that universal claim was stated in this repository.

More generally, for a finitely generated infinite simple MIF group S,
the faithful BFFHZ action image is finitely presented if and only if S
is finitely presented. Choosing an MIF core which is not finitely
presented cannot make this action into a type-(A) action.

This does not refute Boone--Higman. It also does not answer BFFHZ's
published Question 3.2, whose base group is already finitely presented.
It does not exclude a construction choosing suitable non-MIF cores and
using their nontrivial action kernels, or other actions and embeddings.

DERIVATION
[[bffhz-computable-core-counterexample-proof]]
