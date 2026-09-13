---
rg: 2
id: finitely-generated-dense-subgroups-of-sl3z-are-fp
kind: claim
title: Every finitely generated Zariski-dense subgroup of SL_3(Z) is finitely presented
distinct_from:
  sl3z-is-coherent: that claim is coherence of the whole group; this is the Zariski-dense case, which together with the established non-dense case gives it
  non-zariski-dense-subgroups-of-sl3z-are-coherent: that is the established complementary case of subgroups whose Zariski closure is proper
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part2.md
---

Let `K <= SL_3(Z)` be finitely generated with Zariski closure `SL_3`. Then
`K` is finitely presented.

If `K` has finite index this is automatic, since `SL_3(Z)` is finitely
presented. The content is the case of Zariski-dense thin subgroups.

## Attempts

- 2026-09-13 (z3-04-sl3z-coherent): the dense subgroups that lie in the tree
  hierarchy are coherent (`sl3z-incoherence-witnesses-are-zariski-dense-thin`).
  Those are the groups acting on trees with virtually solvable edge
  stabilizers and non-dense or already-covered vertex stabilizers.
- Live cases, either answer possible:
  - (L1) dense thin `K` with a finitely generated normal fibre of infinite
    index; the fibre must be dense too
    (`sl3z-infinite-index-normal-fibers-force-zariski-density`);
  - (L2) virtually RFRS dense thin `K` with `cd_Q <= 2`, where finite
    presentation fails only if `b_2^(2)(K) > 0`
    (`sl3z-coherence-forces-rfrs-cd2-subgroups-free-by-cyclic`);
  - (L3) one-ended dense thin subgroups splitting over no virtually solvable
    subgroup. No method is known here.
