# Mixed finite-subgroup defects need infinite generation

Lane `w3-kap-kernel`, 2026-09-12. Supports the claim
`mixed-finite-subgroup-defects-need-infinite-generation`.

## Context

By `leavitt-inverse-defects-are-visible-or-invisible` and
`leavitt-evaluation-kernel-unitization-not-directly-finite`, a Kaplansky
counterexample for `R^x = L_(F_2)(1,2)^x` reduces to a nonzero defect idempotent
`d = I - AB` with `BA = I` in `M_n(F_2[R^x])`, and it may be taken invisible
(in the kernel of evaluation). The finite-subgroup route builds `d` from the
finite-subgroup idempotents of `F_2[R^x]`, which are abundant
(`leavitt-recursive-kernel-idempotents`). A single finite subgroup is excluded
already: `lifted-trace-detects-finite-subgroup-projectives` shows the lifted
trace is positive on any nonzero projective induced from one finite subgroup,
while a defect has lifted trace zero. `gk-l3-kernel` recorded the next shape:
`d = e - f` with `f < e` from two *different* finite subgroups of equal lifted
trace.

## 1. The finite-join case

**Theorem.** Let `H_1, H_2 <= G` be finite, `e in M_n(F_p[H_1])`,
`f in M_n(F_p[H_2])` idempotents with `f <= e` and `f != e`. If `H = <H_1, H_2>` is
finite, then `e - f` is not a Kaplansky defect. (`f = e` must be excluded: then
`e - f = 0 = I - AB` with `A = B = I`. Corrected after `w3-vf-linear` Section 9.1.)

*Proof.* `e, f in M_n(F_p[H])` with `H` finite, so `e - f` is a nonzero
idempotent of `M_n(F_p[H])`. The lifted trace `t_p` is additive and, on
finite-subgroup projectives, given by `t_p([c]) = dim_(F_p)(c F_p[H]^n)/|H|`,
which is `> 0` for `c != 0`. So
`t_p([(e - f) F_p[G]^n]) = t_p([e]) - t_p([f]) > 0`. A defect `d = I - AB`
(`BA = I`) has `[d F_p[G]^n] = [F_p[G]^n] - [(AB) F_p[G]^n] = 0`, hence
`t_p = 0`. Contradiction. QED

The same argument, with `H_1 = H_2 = H`, is the single-subgroup consequence 1
of `lifted-trace-detects-finite-subgroup-projectives`; the only new content is
that two subgroups with a finite join collapse to that case.

## 2. Candidate idempotents tested

Each candidate below has a finite join, so Section 1 excludes it. This is why
none produced a defect.

- **Order-5 cyclic constants** in a `GL_4(F_2)`-type block and **order-3
  constants** `z = [1]+[g]+[g^2]` (`g = uv`): the two cyclic groups generate a
  finite subgroup of the constant copy `S_3 = <u, v>` or of a fixed level
  matrix group `M_(2^k)(F_2)^x`. Finite join.
- **Level-2 Klein constants** and **dyadic permutation constants** at one
  prefix depth: all lie in a single finite `M_(2^k)(F_2)^x`. Finite join.
- **Two Klein groups at the same level**: still inside one `M_(2^k)(F_2)^x`.

Candidates with an infinite join, for example a level-`j` constant group together
with a Thompson-type unit conjugating across scales, are excluded as well; see
Section 3.

## 3. Where it stops (corrected)

This section originally said the infinite-join case is open, because `t_p` of
`e - f` is not a finite-group dimension count. That was wrong. By additivity
`t_p([e - f]) = t_p([e]) - t_p([f])`, and each term is given by LFT1 in its own
finite subgroup. `nested-two-finite-subgroup-idempotents-have-strict-rank`
(established 2026-09-07) makes that difference strictly positive at any join, so
no nested finite-subgroup difference is ever a defect (flagged by `w4-kap-join`;
`w3-vf-linear` Section 12.3). Section 1 is its finite-join special case.
