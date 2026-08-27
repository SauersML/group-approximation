---
rg: 2
id: kl-packet-inner-breaks-prefix-tree-induction
kind: claim
title: The mixed KL packet breaks prefix-tree induction at the two-leaf split
artifacts:
  - research/kl-packet-inner-breaks-prefix-tree-induction-proof.md
distinct_from:
  degree-four-kl-inner-retractions-fail: that rejects two large bounded families by exact moved vectors; this proves why those finite screens cannot be promoted by a commutative prefix-partition induction.
  leavitt-corners-cannot-compress-external-variable: that concerns applying ring corners to an arbitrary external stable letter; this concerns genuine corner endomorphisms of full coefficient copies and their noncommuting support idempotents.
---

Let `iota_0,iota_1` be the two primitive Leavitt prefix-corner embeddings and
let `q=x_34(s_1)x_(11,12)(t_0)`.  The supports of

```text
Ad(q) o iota_0       and       iota_1
```

do not commute.  This already occurs for the minimal prefix tree `{0,1}`.
Consequently the degree-four `R1` relation cannot be split into independent
prefix leaves after allowing coordinate-`q` inner conjugators.  The
zero-survivor primitive and three-leaf screens therefore do not admit the
proposed induction on finite binary prefix trees.

Even with no outer packet conjugator, the fixed zeroth coefficient copy in
`R1` contains prefix insertion/deletion operators and the solved pivot `z`;
these need not preserve the support partition of the other three copies.
An all-depth theorem needs a genuinely noncommutative projection invariant,
not a common untouched cylinder or blockwise reduction.

The first such candidate, the directed zero/nonzero incidence matrix
`1_(P_iP_j!=0)`, is not invariant under the allowed semigroup either.  The
same two-leaf calculation changes an orthogonal pair into a one-sided pair
with `P_0P_1=0` but `P_1P_0!=0`.  Nor can a fixed finite window of literal
Bergman path-pair coefficients be invariant: an arbitrarily deep prefix
corner shifts every active path pair outside that window.  Any viable
invariant must therefore be renormalized across all prefix scales.
