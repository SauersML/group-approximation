---
rg: 2
id: agent-free-compressor-toeplitz-cell-shift-lef-proof
kind: route
title: Periodize a bounded cell window before taking the regular representation
target: agent-free-compressor-toeplitz-cell-shift-window-is-lef
requires: []
---

Fix a finite subset of the restricted wreath product
`L_p=H_p wr Z`. All coordinate supports and all shift exponents occurring in
this subset and in its multiplication table lie in a bounded interval. Choose
`N` longer than twice that interval and reduce the shift exponent and
coordinate labels modulo `N`. No two inspected coordinates collide and no
inspected shift exponent wraps, so the resulting map into
`H_p^N semidirect C_N` preserves the complete inspected multiplication table
and is injective there. This proves residual finiteness, hence the stated
finite-window models. In the finite group's left regular representation every
nonidentity element has trace zero, so the surviving base center has
normalized-HS distance `sqrt(2)` from the identity.
