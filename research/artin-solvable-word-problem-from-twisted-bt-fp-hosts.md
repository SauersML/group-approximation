---
rg: 2
id: artin-solvable-word-problem-from-twisted-bt-fp-hosts
kind: route
title: If every AV_A embeds in a finitely presented group then every Artin group has solvable word problem
target: every-artin-group-has-solvable-word-problem
requires:
  - every-artin-twisted-brin-thompson-group-embeds-in-fp-group
  - self-twisted-bt-group-fp-embedding-iff-solvable-wp
---

Apply (1)⇒(4) of `self-twisted-bt-group-fp-embedding-iff-solvable-wp` to each Artin
group `A`. This is Zaremsky's own remark: "If so, then this would prove that Artin
groups have solvable word problem."

**Cycle note.** Together with `artin-twisted-bt-fp-hosts-from-solvable-word-problem`,
this route makes a dependency cycle between
`every-artin-twisted-brin-thompson-group-embeds-in-fp-group` and
`every-artin-group-has-solvable-word-problem`, and `cairn check` warns about it. The
cycle records an equivalence. A least fixpoint never fires through a cycle, so neither
claim establishes itself. Do not delete either route.
