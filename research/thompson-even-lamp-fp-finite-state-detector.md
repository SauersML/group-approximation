---
rg: 2
id: thompson-even-lamp-fp-finite-state-detector
kind: claim
title: The Thompson even-lamp group is finitely presented and has only trivial finite-dimensional unitary representations
distinct_from:
  infinite-character-actor-kills-fd-mark: that adds one Pauli seed and kills its mark from infinite character orbits; this uses the Thompson augmentation module itself and kills the entire representation.
  four-cap-three-actuator-destroys-all-fd-packet-evaluations: that amalgamates a Thompson actuator into a finite Pauli packet; this is the intrinsic semidirect-product finite-state detector.
  augmentation-lamp-finite-presentation-criterion: that is the generic finite-presentation criterion; this specializes it to Thompson V and adds exact triviality of every finite-dimensional unitary representation.
  finitary-alternating-augmentation-lamp-global-rounding-no-go: that gives a locally finite amenable counterexample to global rounding; this uses finitely presented Thompson V and records the exact finite-state endpoint whose approximate rounding remains open.
artifacts:
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
---

Let Thompson's infinite simple group `V` act highly transitively on its
countable rational Cantor orbit `X`, and put

```text
I_X = ker(sum : F_2^(X) -> F_2),
Gamma_state = I_X semidirect V.
```

The permutational wreath product `F_2^(X) semidirect V` is finitely presented:
`V` and `C_2` are finitely presented, a point stabilizer is finitely generated,
and the diagonal action on `X^2` has finitely many orbits.  `Gamma_state` is its
index-two subgroup, so it is finitely presented.

Every exact finite-dimensional unitary representation is trivial.  The lamp
involutions have a finite joint character support, and covariance makes it a
finite `V`-set.  Since `V` is infinite simple it has no nontrivial finite
action, so every supporting character is fixed.  A fixed character of `I_X`
extends to a function `X -> F_2` modulo constants; the resulting defect is a
homomorphism `V -> F_2`, hence zero, and transitivity makes the function
constant.  Thus the character is trivial and the lamp image vanishes.  The
remaining image of `V` vanishes by simplicity and Malcev residual finiteness of
finitely generated linear groups.

This is an exact finite-state theorem, not yet an MF theorem.  The Thompson
action, finite-presentation criterion, and joint-character argument remain to
be packaged in Lean.
