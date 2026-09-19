---
rg: 2
id: atlas-word-19243-is-kernel-relation
kind: claim
title: Collision word 19243 lies in the kernel of the two-chart Leavitt map
artifacts:
  - experiments/atlas-word-19243.json
  - experiments/atlas_word_19243_trace.py
  - notes/ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md
---

Let

```text
bar_rho : bar_P = K_1 * K_2 -> Q=L_(F_2)(1,2)^x
```

be the canonical two-chart map.  The explicit eight-syllable collision word
`q_19243` recorded in `experiments/atlas-word-19243.json` satisfies

```text
bar_rho(q_19243)=1.
```

Equivalently,

```text
q_19243 in ker(bar_rho).
```

This is the interior word used by the rank-three exact audit: at the classical
finite `A_8` chart fold it need not evaluate to the identity, even though its
image in the actual Leavitt unit group is the identity.  That mismatch is what
makes its centrality commutator a useful interior separator.