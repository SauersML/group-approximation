---
rg: 2
id: formalizability-conormal-obstruction-is-jacobian-cokernel
kind: claim
title: The leading part of the formalizability obstruction is a Jacobian cokernel over the Boolean group ring, specializing to the Kaplansky matrix
distinct_from:
  formalizability-is-a-boolean-ideal-cokernel-class: that is the exact cokernel reformulation over the whole Boolean ideal; this computes its top graded piece and identifies the operator there with the reduced Jacobian.
  formal-polynomial-strict-pairs-need-unstable-linearization: that linearizes a formal identity at one constant configuration to a matrix over F_2[G]; this shows that matrix is the constant slice of the conormal action of the encoder lift, over every configuration at once.
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
---

Notation as in `formalizability-is-a-boolean-ideal-cokernel-class`. Filter the
Boolean ideal `I` by its powers.

**Claim.**
1. The conormal module `I/I^2` is a free `B`-module on the classes
   `u_h = X_h^2 + X_h`, via the isomorphism `d : I/I^2 -> (+)_h B dX_h`, `u_h -> dX_h`.
2. The encoder lift `hat tau^*` acts on `I/I^2`, in the basis `{u_h}`, by the reduced
   Jacobian `J_B = (partial hat mu_h / partial X_{h'} mod I)`, an equivariant
   finite-memory operator in `M_n(B rtimes G)`.
3. The image of the obstruction class `[eps]` in
   `coker(J_B : (+)_h B dX_h -> (+)_h B dX_h)` is the leading part of the
   formalizability obstruction; it vanishes if `J_B` is a surjective
   `B rtimes G`-operator.
4. Evaluating the Boolean entries at any constant configuration `c in F_2^n`
   specializes `J_B` to `J_tau(c) in M_n(F_2[G])`, the linearization of
   `formal-polynomial-strict-pairs-need-unstable-linearization`. So the constant
   slice of the leading obstruction is `coker(J_tau(c))` over `F_2[G]`, which is `0`
   iff `J_tau(c)` is a split epimorphism.

This is the precise junction between formalizability and Kaplansky: the top graded
piece of the obstruction is a Jacobian cokernel over the Boolean group ring, and its
constant slice is the `M_n(F_2[G])` cokernel already known to control the linear
layer.

## Attempts

- **Proved,** by `formalizability-conormal-jacobian-cokernel-proof`: the de Rham
  computation `Omega_B = 0` in characteristic `2` and `d(u_h) = dX_h`, giving the
  free conormal module; the chain-rule identity for `hat tau^*(u_h)`; and the
  constant specialization to `J_tau(c)`.
- **Consequence used elsewhere:** on a host with `M_n(F_2[G])` directly finite, the
  constant slice is a split epimorphism, so any nonvanishing formalizability
  obstruction lives in the higher `I`-adic layers `I^k/I^{k+1}` (`k >= 2`), the
  collapse-essential regime.
- **Open:** the higher layers are each free `B`-modules under the same operator, but
  their cokernels are not computed here.
