---
rg: 2
id: unsolvable-relative-quotient-via-direct-padded-rn
kind: route
title: The direct padded RN witness itself is a relatively simple counterexample without a further twisted Brin Thompson envelope
target: fp-relatively-simple-pair-with-unsolvable-simple-quotient
requires:
  - padded-abstract-rn-perfect-decidable-nonrecursive-kernel
artifacts:
  - research/artifacts/padded-abstract-rn-manuscript-integration-2026-09-20.md
---

Use `(H,M)=(E,M)` from the prerequisite. It is finitely presented and
relatively simple. Its finitely generated simple quotient is not recursively
presentable, so in particular it has unsolvable word problem: a decision
algorithm would enumerate all relators on its finite generating tuple and
provide a recursive presentation. Item 5 excludes every exact pair
embedding into a finitely presented group with finitely normally generated
normal subgroup, and therefore excludes the relatively simple target pairs
in the claim. No extra abstract twisted Brin–Thompson construction is used.

This is an alternative conditional route into an older existential claim;
it does not certify the stronger prerequisite from that older conclusion.
