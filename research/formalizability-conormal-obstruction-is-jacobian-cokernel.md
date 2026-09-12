---
rg: 2
id: formalizability-conormal-obstruction-is-jacobian-cokernel
kind: claim
title: The leading part of the formalizability obstruction is a Jacobian row-span cokernel over the Boolean algebra, specializing to the Kaplansky matrix
distinct_from:
  formalizability-is-a-boolean-ideal-cokernel-class: that is the exact cokernel reformulation over the whole Boolean ideal; this computes its conormal layer and identifies the operator there with the reduced Jacobian.
  formal-polynomial-strict-pairs-need-unstable-linearization: that linearizes a formal identity at one constant configuration to a matrix over F_2[G]; this shows that matrix is the constant slice of the conormal action of the encoder lift, over every configuration at once.
artifacts:
  - research/artifacts/formalizability-obstruction-class-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Notation as in `formalizability-is-a-boolean-ideal-cokernel-class`, with
`sigma o tau = id`, so `tau^*` is onto `B`.

**Claim.**
1. The conormal module `I/I^2` is a free `B`-module on the classes `u_h = X_h^2 + X_h`,
   via the isomorphism `d : I/I^2 -> (+)_h B dX_h`, `[u_h] -> dX_h`.
2. The encoder lift `hat tau^*` induces on `I/I^2` the `tau^*`-semilinear map
   `[r u_h] -> tau^*(bar r) sum_{h'} J_{h h'} [u_{h'}]`, where
   `J_{h h'} = (partial hat mu_h / partial X_{h'}) mod I` is the reduced Jacobian.
3. Since `tau^*` is onto, the image is the `B`-span of the Jacobian rows. The leading
   part of the obstruction is the image of `[eps mod I^2]` in
   `C = ((+)_h B [u_h]) / (B-span of the rows)`. Its vanishing is necessary for
   formalizability with this encoder representative.
4. Base change along evaluation at a constant configuration `c` gives
   `C (x) F_2 = F_2[G]^n / (row module of J_tau(c))`, where `J_tau(c) in M_n(F_2[G])` is
   the linearization of `formal-polynomial-strict-pairs-need-unstable-linearization`. It
   is `0` iff `X J_tau(c) = 1` for some `X in M_n(F_2[G])`.
5. The leading part is not an invariant of the pair. Some encoder representative has
   `J_B = I` (Lemma C of gk-fz-bennett), and for it `C = 0`.

## Attempts

- **Proved,** by `formalizability-conormal-jacobian-cokernel-proof`: the free conormal
  module; the semilinear Jacobian action; the row-span image; the constant slice; and
  item 5.
- **Correction (after 67b22531e2):** the first version called the induced map
  `B`-linear and said that on a host with `M_n(F_2[G])` directly finite "the constant
  slice is a split epimorphism". Both were wrong for a fixed encoder representative. The
  map is semilinear, and the leading part is killed by choosing the representative, not
  by direct finiteness.
- **Higher layers:** with a Lemma C representative every graded layer `I^k/I^{k+1}`
  vanishes too, so the whole obstruction is termination
  (`binary-left-inverse-pairs-are-boolean-adically-formalizable`).
