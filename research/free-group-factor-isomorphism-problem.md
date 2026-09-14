---
rg: 2
id: free-group-factor-isomorphism-problem
kind: claim
title: Decide whether the free group factors L(F_m) and L(F_n) are isomorphic for distinct m, n >= 2
artifacts:
  - research/artifacts/hl-free-group-factors-2026-09-13.md
distinct_from:
  free-group-factor-elementary-equivalence-problem: that asks for elementary equivalence of the free group factors; this asks for isomorphism.
---

**OPEN.** Are `L(F_m)` and `L(F_n)` isomorphic for some (equivalently, by
`free-group-factor-alternative`, for all) distinct `m, n >= 2`?

Source pins, verbatim:

- Dykema, arXiv:funct-an/9211012, l.130–136: "One hopes to eventually be able to solve the old isomorphism question, first raised by R.V\. Kadison in the 1960's, of whether $L(\freeF_n)\cong L(\freeF_m)$ for $n\neq m$."
- Goldbring–Pi, arXiv:2305.08168, introduction: "A long-standing question regarding the free group factors $L(\F_n)$ for $n \geq 2$, originally considered by Murray and von Neumann in \cite{MvN43}, is whether $L(\F_m) \cong L(\F_n)$ for distinct $m,n \geq 2$."

Structure on main:

- `interpolated-free-group-factor-compression-formula`: all `L(F_r)`,
  `1 < r < infinity`, are amplifications of one another.
- `free-group-factor-alternative`: one isomorphism between two distinct `L(F_r)`
  forces all of them to be isomorphic with fundamental group `R_+`; one
  non-isomorphism forces pairwise non-isomorphism.
- `surface-group-factors-are-free-group-factors`: `L(pi_1(Sigma_g)) = L(F_{2g-1})`
  (preprint), so any separating invariant must agree on these.

## Attempts

1. **1-bounded entropy.** Generator-independent (Hayes; imported in
   `cartan-algebras-are-strongly-one-bounded`), but it equals `+infinity` as soon
   as some generating tuple has `delta_0 > 1` (Hayes Property 6, pinned there).
   So it takes the same value on every `L(F_r)` and cannot separate. *Dead as a
   separating invariant.*
2. **Structure theorems from the Peterson–Thom resolution.** Hayes–Jekel–
   Kunnawalkam Elayavalli (arXiv:2308.14109) prove coarseness of maximal amenable
   subalgebras, a strong-solidity generalization, and a Pinsker-type
   intertwining dichotomy. Each is stated "for `t > 1`" uniformly in the TeX
   (Theorems `thm:coarseness intro`, `intro thm: solidity`,
   `thm:Pinkser dichotomy intro`), so none distinguishes parameters. *No
   separation.*
3. **Free entropy dimension `delta_0`.** It would separate if it were an
   invariant: the free generators of `L(F_n)` give `n`. Generator independence
   is the missing step. Not pinned at source here; the known partial invariance
   is Jung's: strong 1-boundedness, i.e. the `delta_0 <= 1` regime, is
   generator-independent (pinned in `cartan-algebras-are-strongly-one-bounded`).
   It says nothing in the regime `delta_0 > 1`, where the free group factors
   live. *Open; this is the classical gap.*
4. **Model theory.** See `free-group-factor-elementary-equivalence-problem`.
   Distinct first-order theories would give non-isomorphism.
   `independent-free-factor-equivalences-force-common-theory` shows two
   log-independent elementary equivalences already force all interpolated free
   group factors to share one theory, so a first-order separation must break at
   the very first comparison.

**Exact gap.** One of:

- a generator-independent quantity that is finite on some `L(F_t)` and depends
  on `t`;
- an explicit isomorphism `L(F_2) = L(F_r)` for one `r != 2`, which by the
  alternative settles everything;
- non-elementary-equivalence of one pair.
