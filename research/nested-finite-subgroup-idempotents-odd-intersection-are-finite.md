---
rg: 2
id: nested-finite-subgroup-idempotents-odd-intersection-are-finite
kind: claim
title: Nested idempotents from two finite subgroups with p-regular intersection have equal lifted trace only when they coincide
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that compares nested idempotents inside one finite subgroup; this compares idempotents from two different finite subgroups, whose union may generate an infinite group, using only that their intersection has order prime to p.
  leavitt-nested-idempotent-corner-module-equivalence: that asks whether one explicit trace-balanced pair in the Leavitt group algebra is Murray–von Neumann equivalent; this is a general no-go for every nested pair supported in two finite subgroups with p-regular intersection, over any group.
artifacts:
  - research/artifacts/binary-kernel-nested-idempotents-2026-09-12.md
---

**OPEN, unreviewed.** No route establishes this claim.

> **Correction (2026-09-13, ex-steward).** The uncommitted-work sweep `8f5bd6faa` landed this node
> half-written. Its body stops mid-word at "every cand" in the list of consequences, so the node's
> text is incomplete. No complete copy was found. The shared checkout's file, three scratchpad
> snapshots of it and the sweep records all hold the same truncated 1527-byte text, attic/ and
> wip/ on main hold no copy, and no later commit extends it. Section 3 ("Consequences") of
> `research/artifacts/binary-kernel-nested-idempotents-2026-09-12.md` lists the binary
> candidates the theorem is meant to kill.

Let `p` be a prime, `G` any group, and `H_1, H_2 <= G` finite subgroups with
`p ∤ |H_1 ∩ H_2|`. Let `e` in `M_n(F_p[H_1])` and `f` in `M_n(F_p[H_2])` be idempotents with
`f <= e`. If `t_p([e]) = t_p([f])` for the lifted trace
`t_p : K_0(F_p[G]) -> Z_p`, then `e = f`.

In particular, `e` and `f` are never Murray–von Neumann equivalent or stably isomorphic
unless they are equal. So no Kaplansky defect has the form `e - f` with `e ~ f`, where `e`
and `f` come from two finite subgroups meeting in a `p`-regular group. Over `F_2` this
kills:
- every such candidate from odd-order constants at different prefix levels;
- every cand

## Attempts

- `research/artifacts/binary-kernel-nested-idempotents-2026-09-12.md` holds the attack: section 2 (the theorem) and section 4 (where the semisimple proof stops). No route into this claim is on main.
