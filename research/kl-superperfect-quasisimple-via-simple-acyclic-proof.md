---
rg: 2
id: kl-superperfect-quasisimple-via-simple-acyclic-proof
kind: route
title: A simple acyclic counterexample is already superperfect and quasisimple with trivial centre
target: kl-counterexample-can-be-superperfect-quasisimple
requires: [kl-counterexample-can-be-two-generator-simple-acyclic]
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

The prerequisite gives a failure over a two-generated infinite simple group
`S` with `H_n(S; Z) = 0` for all `n >= 1`.
- **Superperfect.** In particular `H_1(S) = H_2(S) = 0`.
- **Quasisimple.** `S` is nonabelian simple, so `Z(S) = 1`, and
  `S/Z(S) = S` is nonabelian simple.

So `S` is the required two-generator superperfect quasisimple counterexample.

This avoids the gap recorded in the target's Correction section. There is no
universal central extension to lift through: `H_2(S) = 0`, so `S` is its own
universal central extension. ∎
