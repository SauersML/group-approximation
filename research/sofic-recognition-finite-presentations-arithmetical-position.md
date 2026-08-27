---
rg: 2
id: sofic-recognition-finite-presentations-arithmetical-position
kind: claim
title: Sofic finite presentations are Pi-zero-two but not Pi-zero-one, and nonsofic ones are Sigma-zero-two but not recursively enumerable
artifacts:
  - GroupApproximation/Computability/SoficRecognitionPi02.lean
  - GroupApproximation/Computability/SoficMarkov.lean
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  mf-recognition-has-a-pi2-upper-bound: that places MF finite presentations in the same strict intervals; this places sofic ones there, with a different upper bound (permutations) and a different forbidden seed (a nonsofic group).
  sofic-recognition-two-generator-recursive-is-pi2-complete: that is a completeness theorem for recursive presentations; this is the finite-presentation statement, where completeness is not claimed because it needs a sofic-safe compiler.
  sofic-recognition-finite-presentations-is-pi2-complete: that is the open completeness statement; this is what is known unconditionally today, a strict-interval placement.
---

ESTABLISHED, unconditionally.  For the recursive coding of finite group
presentations,

```text
SOFIC_fp     in Pi^0_2    \ Pi^0_1,
NONSOFIC_fp  in Sigma^0_2 \ Sigma^0_1.                                (SP1)
```

So no algorithm decides soficity of a finitely presented group, the
nonsofic finite presentations cannot be enumerated, the sofic ones cannot be
co-enumerated, and both sets lie at most one level higher.  The lower
half is `Computability/SoficMarkov.sofic_recognition_undecidable` and
`sofic_negative_side_not_re`; the upper half is the permutation certificate.

Whether `SOFIC_fp` is `Pi^0_2`-complete is
[[sofic-recognition-finite-presentations-is-pi2-complete]].

**Machine-checked.**  `SoficRecognitionPi02.sofic_fp_strict_position` is
exactly (SP1): `Pi02` and not `Pi01` for sofic codes, `Sigma02` and not
`Sigma01` for nonsofic codes.
