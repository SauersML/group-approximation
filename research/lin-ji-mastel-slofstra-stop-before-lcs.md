---
rg: 2
id: lin-ji-mastel-slofstra-stop-before-lcs
kind: claim
title: Lin plus low-degree soundness and weighted BCS reductions stop before LCS syntax
artifacts:
  - research/artifacts/lin-ji-mastel-slofstra-bcs-lcs-boundary-2026-08-23.md
distinct_from:
  lin-gap-wrappers-retain-oracular-atlas-holonomy: that analyzes the projection atlas of Lin's separated game when its perfect strategy is oracularizable; this claim distinguishes the unconditional fixed-game BCS conversion from the efficient oracularized protocol conversion and then isolates the BCS-versus-LCS boundary.
  lin-explicit-fixed-bcs-gap-via-generic-conversion: that positively closes the fixed finite BCS step; this audits why the result still stops before affine LCS syntax.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for the missing machine-indexed LCS compiler; this identifies exactly why the three supplied sources do not furnish it.
  mastel-slofstra-private-context-augmentation-preserves-defect: that is one positive weighted BCS transformation; this audits the complete source chain and its endpoint.
---

**ESTABLISHED by primary-source audit.**  Ji--Natarajan--Vidick--Wright--Yuen
Theorems 1.3 and 3.10 supply global low-individual-degree polynomial
measurements with quantitative consistency error.  They do not supply BCS or
LCS syntax.

Lin Theorem 6.15 supplies finite synchronous games in the separated promise
class

```text
omega_co(G)=1,                 omega_*(G)<=1/2.            (LMS1)
```

Its theorem statement does not assert that the perfect commuting strategy is
oracularizable.  Lin Theorem 6.5 preserves perfect oracularizable strategies
conditionally on their existence; value one and synchrony alone do not imply
same-algebra commutation of the two question PVMs.  This matters for the
efficient oracularization route, but not for a fixed finite BCS conversion.

Before Lemma 3.1, Mastel--Slofstra give an unconditional construction from
every synchronous game to a BCS using variables `x_(i,a)`, one-answer
constraints, and losing-pair constraints.  Perfect quantum,
quantum-approximable, and commuting strategies are preserved in both
directions, and the paper records an answer-size-dependent quantitative
soundness loss.  Applied to the fixed effective `G_loop`, this gives
`B_loop` with

```text
omega_co(B_loop)=1,           omega_q(B_loop)<=1-delta_loop. (LMS2)
```

Here `delta_loop>0`; exponential answer blowup is harmless for one fixed
finite game.  Lemma 3.1 and the subsequent oracular BCS construction are the
efficient alternative for protocol families and still require perfect
oracularizable completeness.

Definitions 4.1--4.2, Lemma 4.3, Lemma 5.2,
Theorem 6.4, and Propositions 8.4--8.5 provide genuine weighted tracial-defect
control through context extension, subdivision, Cook--Levin/3SAT encoding,
and the tableau construction.  Theorem 8.8 only converts an already existing
inverse-polynomial-gap `BCS-MIPco` protocol to PZK; it does not prove
`MIPco=BCS-MIPco`.

None of the three sources gives a weighted homomorphism or robust decoder from
the resulting arbitrary Boolean/3SAT predicates to affine parity constraints.
Thus `(LMS2)` is unconditional for the fixed loop game, but its output is not
an LCS, has no associated LCS
solution group, and does not close
`perfect-completeness-constant-soundness-lcs-compiler`.  The exact remaining
theorem is a dimension-independent general-BCS-to-LCS (or mark-relative
BCS-to-group) defect decoder; exact satisfiability preservation alone is
insufficient.

## Attempts

- Treat Theorem 6.15's value-one synchronous strategy as automatically
  oracularizable: rejected because left/right commutation in the commuting
  model does not imply commutation of two question PVMs in the one-player
  tracial algebra.  This blocks the efficient oracularized conversion, not
  the unconditional fixed-game one-hot/losing-pair construction.
- Invoke Mastel--Slofstra Theorem 8.8 as `MIPco=BCS-MIPco`: rejected because
  both sides of that theorem already carry the `BCS-` restriction.
- Read Cook--Levin/3SAT subdivision as linearization: rejected because
  Propositions 8.4--8.5 preserve general Boolean constraints, not affine
  parity support or solution-group relators.
