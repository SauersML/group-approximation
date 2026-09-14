---
rg: 2
id: non-mf-hyperbolic-group
kind: claim
title: A word-hyperbolic group that is not MF
distinct_from:
  non-residually-finite-hyperbolic-group: for one group, failing MF is strictly stronger than failing residual finiteness; as existence questions the two are equivalent by hyperbolic-rf-question-equals-non-mf-question
  relative-hull-quotient-with-full-mf-radical: that produces acylindrically hyperbolic Kazhdan groups with full MF radical, which are not word-hyperbolic in general; this demands word-hyperbolicity
---

Exhibit a word-hyperbolic group that is not operator MF (norm-matrix-corona
sense of `countable-group-mf-conventions`).

This is Gromov's residual-finiteness question transported into the
repository's MF program: by `hyperbolic-rf-question-equals-non-mf-question`, a
non-MF hyperbolic group exists iff a non-residually-finite one does.  So this
repository's non-MF theorem for finitely presented groups cannot be upgraded
to word-hyperbolic witnesses without answering Gromov's question negatively.
Conversely, a proof that every hyperbolic group is MF **would** settle Gromov's
question positively.  For one group MF is much weaker than residual
finiteness, but quantified over all hyperbolic groups the two statements are
equivalent: if some hyperbolic group were not residually finite, the Kazhdan
common quotient of `hyperbolic-rf-question-equals-non-mf-question-proof`
would be a hyperbolic group that is not MF.  The same argument, stopping at
Ozawa--Thom's weak quasidiagonality hypothesis, shows that "every hyperbolic
group is weakly quasidiagonal" is also equivalent to universal residual
finiteness.

## Attempts

- **From a Kazhdan hyperbolic group without finite quotients.**
  `non-mf-hyperbolic-from-kazhdan-quotientless` is complete (Ozawa--Thom), and
  that input follows from any non-residually-finite hyperbolic group, so this
  claim is exactly as hard as Gromov's question.
- **The repository's non-MF mechanisms.**  The full-MF-radical witnesses here
  are produced by Hull's small cancellation and are only acylindrically
  hyperbolic (see `relative-hull-quotient-with-full-mf-radical`); word
  hyperbolicity is not preserved by those constructions (audit §B.7 in
  `research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md`).
  The Kun--Thom compression witnesses are excluded in a hyperbolic ambient
  group by the centralizer rigidity of audit §B.1.  Whether the operator-norm
  compression mechanism itself can run inside a word-hyperbolic group is not
  decided here.
