---
rg: 2
id: lin-explicit-fixed-bcs-gap-via-generic-conversion
kind: claim
title: Lin's loop game has an effectively named fixed BCS with a commuting/quantum gap
artifacts:
  - research/artifacts/lin-ji-mastel-slofstra-bcs-lcs-boundary-2026-08-23.md
  - research/artifacts/cmps-smooth-label-monomial-audit-2026-08-23.md
distinct_from:
  lin-explicit-synchronous-bell-gap-game: that outputs a general synchronous game; this applies the unconditional finite BCS conversion.
  mipstar-bcs-tracial-nonru-exists: that is an existential BCS consequence of MIPstar=RE; this gives an effectively named BCS from a fixed known nonhalting program.
  oracularizable-tracial-nonru-game-exists: that adds an incidence/oracular interface to a BCS source; this fixed-game conversion does not require or assert an oracularizable source strategy.
  lin-ji-mastel-slofstra-stop-before-lcs: that audits why weighted BCS transformations do not reach affine LCS syntax; this positively closes only the fixed finite game-to-BCS step.
---

**ESTABLISHED FIXED-GAME CONVERSION.**  There is an effectively specified
finite Boolean constraint system `B_loop` and a constant `delta_loop>0` with

```text
omega_co(B_loop)=1,
omega_q^s(B_loop)<=1-delta_loop.                         (LBC1)
```

Apply the unconditional synchronous-game-to-BCS construction in
Mastel--Slofstra Section 3 to `G_loop`: introduce Boolean variables `x_(i,a)`,
one-answer constraints for each question, and a binary forbidden-pair
constraint whenever `V(a,b|i,j)=0`.  The paper states that the resulting BCS
has a perfect quantum, quantum-approximable, or commuting strategy if and
only if the original game does, and records the quantitative soundness loss
as exponential in the original answer length.

Lin gives `omega_q(G_loop)<=1/2`, and all question and answer sets of this
one game are finite and effectively known.  The stated finite loss therefore
leaves the strict constant `delta_loop`; perfect commuting equivalence gives
the first line of `(LBC1)`.

The construction may have exponentially long BCS answers and is not an
efficient conversion of an arbitrary protocol family.  That is irrelevant
for this fixed finite source but is exactly why Mastel--Slofstra subsequently
use oracularization for their complexity-theoretic protocol result.
