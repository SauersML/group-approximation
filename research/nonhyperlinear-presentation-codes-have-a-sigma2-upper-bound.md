---
rg: 2
id: nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound
kind: claim
title: Nonhyperlinear finite-presentation codes have a Sigma-zero-two upper bound
artifacts:
  - research/artifacts/computer-science-framing-audit-2026-08-21.md
distinct_from:
  word-problem-of-finite-presentation-is-re: that semidecides equality of one word by a finite derivation; this combines such derivations with decidable finite-dimensional semialgebraic feasibility and one quantifier over microstate scales.
  mf-recognition-undecidable: that concerns MF recognition and proves undecidability consequences by a separate Markov-property reduction; this gives only an arithmetical-hierarchy membership bound for hyperlinearity and proves no matching hardness.
  taller-vidick-lcs-re-hardness: that is an RE-hard promise problem for values of LCS games; this classifies the quantifier form of presentation recognition and does not transfer the game's hardness to groups.
---

For codes of finite group presentations,

```text
HYP is in Pi^0_2,             non-HYP is in Sigma^0_2.      (NHS1)
```

At scale `n`, list the finitely many words of length at most `n`.  A finite
certificate consists of:

1. a partition of that list into words declared trivial and words to be
   separated;
2. a finite van Kampen derivation for every word declared trivial;
3. a dimension `d` for which the semialgebraic system asking for unitary
   generator matrices, relator defect below `1/n`, and squared distance from
   the identity above `2-1/n` for every remaining word is feasible.

For fixed finite data and `d`, validity is decidable: derivations are finite
word calculations and feasibility is a first-order sentence over the real
closed field of real and imaginary matrix entries.  Hyperlinearity is
equivalent to

```text
for every scale n there exists such a finite certificate.             (NHS2)
```

This proves `(NHS1)`.  The result is an **upper bound**, not an exact
classification.  In particular it does not prove `Sigma^0_2`-hardness or
completeness for nonhyperlinear presentations.  It also does not make that
set recursively enumerable: an `exists n, for all certificates/dimensions`
condition is generally one level above semidecidability.
