---
rg: 2
id: deepest-match-orientation
kind: claim
title: The landing chunk's deepest eaten letters are always matched relator-vs-relator
distinct_from:
  greendlinger-free-product-lemma: that is the open gate itself; this is a small established positional fact about minimal expressions that splits the gate's landing analysis into a piece-bounded part and a conjugator part.
artifacts:
  - GroupApproximation/Sofic/GreendlingerCascade.lean
  - GroupApproximation/Sofic/GreendlingerChunks.lean
---

In the CascadeLanding regime (minimal expression `(c₁,t₁) :: e'`,
reduced head palindrome, eaten suffix `M` with `|c₁| < |M|`), the eaten
prefix of the tail word is `invRev M = c₁ ++ invRev(t₁-suffix of
length μ)` with `μ = |M| − |c₁| ≥ 1`: conjugator letters occupy the
SHALLOW eaten positions `[0, |c₁|)` and head-relator letters the DEEP
positions `[|c₁|, |c₁|+μ)`.  Hence the landing chunk — the chunk of the
tail's decomposition containing the last eaten position — always ends
its eaten part matched against letters of `t₁`, never of `c₁`.

Consequence: the intrusion `i` of the eaten block past the landing
factor's conjugator splits as `i = i_c + i_t` with `i_t ≥ 1`, where the
`i_t` letters are a common subword of rotations of `t₁` and `t_j` —
piece-bounded by `isPiece_of_overlap` or collapsed by the coincidence
lemmas — and only `i_c` (head-conjugator overrun through ALL
intermediate chunks) escapes the piece calculus.  The open
[[greendlinger-free-product-lemma]] landing analysis thereby reduces to
the `i_c > 0` regime; see notes/W1_GREENDLINGER_GATE_DESIGN_2026-08-21.md
for the case tree, the mandatory adversarial test of that regime, and
the candidate closures.
