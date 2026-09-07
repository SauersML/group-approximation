---
rg: 2
id: fixed-hs-word-gap-is-linear-domination
kind: claim
title: A fixed scalar-sensitive Hilbert--Schmidt word gap is equivalent to global linear domination
distinct_from:
  character-domination-collapse-equivalences: that uses the projective character defect 1-|chi|^2, which kills scalar phases; this gives an ordinary HS word bound and the explicit constant 2/eta from a distance-one gap.
  padding-makes-local-hs-rigidity-global: that assumes a linear estimate near the identity and preserves its constant by padding; this starts from one fixed separated-word gap and derives linearity by a real-trace tensor transform.
  matrix-phase-linear-alpha-plane-inequality: that concerns slope energies in finite-field tables; this treats arbitrary free-group relators and one word, without affine averaging.
artifacts:
  - research/artifacts/hs-word-gap-linearization-2026-09-07.md
  - experiments/hs_word_gap_amplification_check.py
  - research/artifacts/hs-word-gap-amplification-replay-2026-09-07.json
---

Let S be finite, R a finite set of words in F(S), and w another word.
Write delta_R(U)=max_(r in R)||r(U)-I||_2 in normalized HS norm, with
the empty maximum equal to zero. If eta>0 and in every finite dimension

```text
||w(U)-I||_2 >= 1  ==>  delta_R(U) >= eta,
```

then for every unitary tuple in every dimension

```text
||w(U)-I||_2 <= (2/eta) delta_R(U).
```

Conversely a global bound with any C>0 gives a gap eta=1/C. The estimate
retains scalar phases. The same equivalence holds with max_(s in S)
||U_s-I||_2 in place of the single word, with the same constants.

This is a proved implication for arbitrary finite word lists. It supplies
no gap for a particular nontrivial group. In particular the hypothesis of
`saturated-group-hs-relator-defect-gap` remains open.
