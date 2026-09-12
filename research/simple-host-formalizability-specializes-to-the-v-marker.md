---
rg: 2
id: simple-host-formalizability-specializes-to-the-v-marker
kind: route
title: Thompson's V is a finitely generated simple host, and the marker involution is a binary left-inverse pair on it
target: thompson-v-marker-involution-is-formalizable
requires:
  - binary-left-inverse-pairs-over-fg-simple-groups-are-formalizable
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

1. **`V` is a finitely generated simple group.** This is classical (Higman; Thompson), imported at
   statement level.
2. **The pair.** `tau_g` is an involution on `{0,1}^V`, so `(tau_g, tau_g)` is a binary left-inverse pair.
3. **Specialize.** The prerequisite gives representatives `tau~` and `sigma~` of `tau_g`, possibly
   different polynomials, with `sigma~ o tau~ = id` formally. That is the target, which is stated in
   pair form.

A refutation of the target therefore refutes the prerequisite.

**Correction** (after `w3-vf-nonlinear`, Section 14 of its verification artifact). The target first
asked for a single representative with `tau~ o tau~ = id`. The prerequisite does not give that, so as
first stated this route was invalid. The target is now in pair form, and the route is re-submitted for
verification.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS after the repair at e0b01243d3.** Step 3 yields exactly the
pair form of the target (`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 14,
follow-up).
