---
rg: 2
id: leavitt-evaluation-has-no-ring-section-proof
kind: route
title: Augment a hypothetical section, then rank over the residue field
target: leavitt-evaluation-has-no-ring-section
requires: []
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

*Scalar case.*  A unital ring section `sigma` places `S_i = sigma(s_i)`,
`T_i = sigma(t_i)` in `F_2[G]` satisfying the binary Leavitt relations.
Compose with the augmentation `eps : F_2[G] -> F_2` and write
`a_i = eps(S_i)`, `b_i = eps(T_i)`.  From `T_0 S_0 = 1`, `b_0 a_0 = 1`, so
`b_0 != 0`.  From `T_0 S_1 = 0`, `b_0 a_1 = 0`, and `F_2` is a domain, so
`a_1 = 0`.  But `T_1 S_1 = 1` gives `b_1 a_1 = 1`, a contradiction.  The
idempotent relation `s_0 t_0 + s_1 t_1 = 1` is never used, so the obstruction
already applies to the half of the relations expressing `R = R (+) R`.

*Matrix case.*  Fix `n >= 1` and suppose `S_i, T_i` in `M_n(F_2[G])` satisfy
the relations.  Apply entrywise augmentation into `M_n(F_2)`.  On the
finite-dimensional space `F_2^n`, `T_0 S_0 = I_n` forces `S_0` invertible
with `T_0 = S_0^(-1)`; then `T_0 S_1 = 0` gives `S_1 = 0`, contradicting
`T_1 S_1 = I_n`.  Finite dimension is what does the work — exactly the step
that fails for `R` itself, which is its own proper matrix amplification.

This is verbatim the argument recorded at
`augmentation-blocks-leavitt-family-proof` with `Z` replaced by `F_2`; both
proofs need only that the augmentation lands in a nonzero commutative ring
with no zero divisors, and that the matrix case is run over its field of
fractions (here `F_2` itself).  It is restated rather than reused because
that node is stated for integral group rings.
