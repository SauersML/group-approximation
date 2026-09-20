---
rg: 2
id: distance-code-local-tests-are-label-diagonal
kind: claim
title: Tests below classical code distance have label-diagonal compression even with shared quantum auxiliaries
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
distinct_from:
  correctable-data-tests-are-logically-blind: That assumes quantum erasure correction and obtains identity on the whole logical space; a classical distance code here only kills off-diagonal blocks and permits label-dependent diagonal blocks.
---

Let C map logical bit strings injectively into M physical bit strings
with minimum Hamming distance D. Let P project onto their span,
tensored with identity on an arbitrary auxiliary register.
For a sum K of operators each touching at most k<D encoded-data bits
and any auxiliary sites, every off-diagonal logical block of PKP is zero:
PKP=sum_x |C(x)><C(x)| tensor K_x.
Dephasing the logical classical label preserves every code-supported
state's energy; K_x may still be quantum and label-dependent.

On the length-three repetition code, no sum touching at most two data
bits distinguishes GHZ+ from GHZ-. The best operator-norm approximation
of logical (I-X)/2 by such a compressed operator has error 1/2,
attained by I/2. This is a fixed-encoding simulation restriction, not
an impossibility of QPCP ground-energy reduction.

