---
rg: 2
id: lin-ji-mastel-slofstra-primary-source-audit
kind: route
title: Audit the Lin, low-individual-degree, and Mastel--Slofstra theorem interfaces
target: lin-ji-mastel-slofstra-stop-before-lcs
requires: []
---

**Established by the supplied primary sources.**

Ji--Natarajan--Vidick--Wright--Yuen Theorems 1.3 and 3.10 are quantitative
measurement-extraction statements.  Lin Theorem 6.5 preserves perfect
oracularizable strategies conditionally, while Theorem 6.15 states only the
synchronous value promise `omega_co=1`, `omega_*<=1/2`.

Mastel--Slofstra Section 3 first gives an unconditional generic
synchronous-game-to-BCS construction with one-answer and losing-pair
constraints.  It preserves perfect quantum, quantum-approximable, and
commuting strategies and has an answer-size-dependent quantitative loss.
For Lin's one fixed finite loop game, this gives an effective BCS with a
strict commuting/quantum gap.  Lemma 3.1 is the different, efficient
oracularization route for protocol families and requires perfect
oracularizable completeness.

Their Definitions 4.1--4.2, Lemmas 4.3 and 5.2, Theorem 6.4, and
Propositions 8.4--8.5 preserve weighted BCS defect through the transformations
they explicitly construct.  Theorem 8.8 starts with `BCS-MIPco` on both sides
and therefore does not establish `MIPco=BCS-MIPco`.  None of the statements
constructs affine parity constraints, an LCS weighted homomorphism, or a
solution group from a general BCS.

The complete statement-by-statement audit, unconditional fixed-game BCS
consequence, and conditional efficient-protocol distinction are in
`research/artifacts/lin-ji-mastel-slofstra-bcs-lcs-boundary-2026-08-23.md`.
