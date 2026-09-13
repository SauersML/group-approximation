---
rg: 2
id: every-turing-degree-is-a-simple-kazhdan-lef-word-problem
kind: claim
title: Every Turing degree is the degree of the word problem of an infinite finitely generated simple Kazhdan LEF group
distinct_from:
  fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees: that realizes every word-problem degree by non-simple Kazhdan extensions of one LEF endpoint group; this realizes every degree by groups that are themselves infinite, simple, Kazhdan and LEF.
  continuum-many-simple-kazhdan-lef-groups: that proves continuum many isomorphism types by counting markings; this separates explicit pairs through the word-problem degree.
  subshift-elementary-group-word-problem-degree: that (2026-09-12, reviewed PASS) already realizes every Turing degree over Sturmian subshifts, and its artifact gives WP(S_X) ≡_T L(X), so the simple groups S_X already realize every degree; this states the simple form as a node.
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

For every prime power `q` and every Turing degree `d`, there is an irrational `α` such that
`S_(X_α) = EL_3(LC(X_α,F_q)⋊Z)/Z`, over the Sturmian subshift `X_α`, is an infinite, finitely generated, simple
group with property (T) that is LEF (hence sofic and hyperlinear), and whose word problem has degree `d`.

In particular:
- the groups `S_(X_α)` with `α` computable (e.g. `α = √2−1`) have solvable word problem;
- `α, β` of different Turing degrees give non-isomorphic groups. Word-problem degree is an isomorphism invariant
  of finitely generated groups.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §1.5): PASS,
subsumed in substance.** The choice `α = 0.1 b_0 1 b_1 1 b_2 …` (irrational, `α ≡_T B`) and the chain
`WP ≡_tt L(X_α) ≡_T α` were re-derived. The degree statement is already on main through
`subshift-elementary-group-word-problem-degree`.
