---
rg: 2
id: c18-child-oriented-gates-follow-the-two-source-words-proof
kind: route
title: Match the target greedily to p, then assign every unmatched occurrence to its child
target: c18-child-oriented-gates-follow-the-two-source-words
requires:
  - oriented-c18-rank-gates-give-branch-balance
  - fanizza-bad-atoms-have-symmetric-frames
artifacts:
  - experiments/fanizza_child_oriented_c18_exit_compiler.py
---

For a phase-even atom, first match a present target `r` to the `p` child when
`p=1`, and otherwise to the `q` child.  The unmatched `p` occurrences are
exactly `p(1-r)`.  The unmatched `q` occurrences are exactly
`q((1-r) or p)`.  The eight-atom truth table gives

```text
e_p+e_q=max(p+q-r,0)=e_1+e_2.
```

The verifier checks this on all 64 assignments, constructs the best OBDD
compiler for each predicate, and applies the exhaustive dual-word frame
search.  The `p` gate has baseline rank 8 and the `q` gate baseline rank 9.
All 20 exact searches return the symmetric kernel code `52789443047427` and
hard form `(0,1,0,0,0,0)`.  Runtime is under 12 seconds and peak memory under
14 MB on one low-priority MSI core.
