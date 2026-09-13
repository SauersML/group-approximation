---
rg: 2
id: rokhlin-window-random-order-transport-identity
kind: claim
title: Decoded information of a Bernoulli window configuration equals a random-order transport into one output
distinct_from:
  injective-ca-random-order-transport-identity: that splits log |A| over the decoder memory of an injective automaton; this splits the decoded information I(x(1); y_F) of an arbitrary window configuration, which is not a constant.
  bernoulli-witness-information-is-bounded-by-code-reads: that bounds I(x(1); y_F) by m H(psi) along the order listing non-readers first; this is an exact identity along an invariant random order, where non-reading codewords contribute.
artifacts:
  - research/artifacts/rokhlin-window-random-order-transport-2026-09-12.md
---
**ESTABLISHED** (artifact Section 2, route `rokhlin-window-transport-identity-proof`). Verified by `w4-vf-positive-b` in Section 9.1 of `research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.

**Setting.**
* `G` is a countable group and `x` is iid uniform on `(A^k)^G`.
* `(k, E, F, psi)` is a configuration of `bernoulli-rokhlin-deficit-has-a-finitary-witness`, with `y_g = psi((x(g e))_(e in E))`.
* `U` is a family of iid uniform labels independent of `x`, and `past(1) = {h : U_h < U_1}`.

Then

    I( x(1) ; y_F ) = sum_(f in F) I( x(f^-1) ; y_1 | y_(f^-1 F ∩ past(1)), U ) .

Expanding the left side by the chain rule over `F` along the order gives one term per codeword, and left translation by `f^-1` moves the `f`-term to the output `y_1`. The proof uses no finite model and no amenability.

**Calibration** (artifact Section 3). On `Z/5` with `E = {0,1,2}`, `psi` the parity map and `F = Z/5`, an order that starts `4 < 1 < 2` gives the non-reading codeword `2` the whole decoded bit. So the terms are not supported on the readers of site `1`.
