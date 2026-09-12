---
rg: 2
id: leavitt-d4-l14-three-winner-boundary-needs-21-blocks-proof
kind: route
title: Dynamic-program the three-winner boundary topology
target: leavitt-d4-l14-three-winner-boundary-needs-21-blocks
requires:
  - leavitt-d4-l14-three-winner-trivial-carrier-is-fenced
---

Expand the literal boundary `H^-1B0 H^-1B1 H^-1E4` from the raw corners and
combine adjacent syllables from the same coefficient copy.  Its copy word is

```text
3,2,1,2,1,2,1,2,1,0,1,2,3,2,3,2,1,2,1,2,1,2,1,0,
1,0,1,2,3,2,1,2,1,2,1,2,1,0,1,2,3.
```

The artifact performs interval dynamic programming over all monochromatic
noncrossing blocks.  MSI job `16678564` returned

```text
syllables=41
minimum_noncrossing_blocks=21
minimizing_partitions=1574216
cached_intervals=778
```

Thus a direct materialization of all minimal coefficient systems is the
wrong next step.  Carrier-equation substitution or a symbolic sparse packet
must prune the 1,574,216 topologies before Tietze replay.

The later all-maximal forest recursion independently returned on MSI job
`16680094`

```text
maximal_forests=1574216
cached_states=778.
```

Thus the all-maximal count equals the minimum-block count exactly.  Every
noncrossing partition coarsens to a maximal one, so for this exact 41-color
word every cancellation branch refines one of the 1,574,216 minimum schemes.
This repairs the general minimum-block inference gap for this word, while
leaving coefficient/Tietze compression as the remaining task.
