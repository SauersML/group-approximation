---
rg: 2
id: effective-free-shift-shell-counterexample-proof
kind: route
title: Combine the effective generic enumeration with certified decision and the finite-presentation obstruction
target: decidable-inputs-have-computable-non-fp-shell-envelopes
requires:
  - regular-enumerations-can-make-near-shift-free-product
  - free-shift-shell-relations-are-finitely-certified
  - free-shift-shell-envelopes-are-not-finitely-presented
  - shell-cantor-embeddings-are-finite-germ-extensions
  - perfect-input-shell-envelopes-are-simple
  - shell-finite-prefix-cannot-certify-presentation
artifacts:
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
---

Extend the prescribed finite partial bijection using the effective
fresh-trajectory construction. It gives computable nu and inverse
with R_nu=P*<s>. The finite-certificate algorithm then decides the
word problem of E_nu. The presentation obstruction proves E_nu
is not finitely presented, independently of this decidability.
Faithfulness and finite generation are part of the shell realization.
For perfect P its simplicity follows from the required simplicity
claim. All these properties refer to the same enumeration.

For a virtually cyclic P, the existing finite-prefix result also
supplies an enumeration extending that prescription with E_nu
finitely presented, by a finite change of a finite-ray enumeration.
Such changes are computable. Thus every finite prescription has
both a computable positive and a computable negative example for
finite presentation of E, even though both examples have decidable
word problem. This strengthens the earlier negative examples that
used noncomputable enumerations and failed recursive presentability.
