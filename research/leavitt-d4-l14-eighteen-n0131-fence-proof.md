---
rg: 2
id: leavitt-d4-l14-eighteen-n0131-fence-proof
kind: route
title: Exhaust the normal 131 carriers and cyclic boundaries
target: leavitt-d4-l14-eighteen-n0131-is-fenced
requires:
  - leavitt-d4-l14-eighteen-n0131-projection-core
  - leavitt-d4-l14-eighteen-i0131-is-fenced
---

MSI job `16686624` applies the audited all-maximal noncrossing forest and
coordinate-state semiring to the exact five-generator core.  The
13-syllable carrier has nine coordinate states, the 39-syllable carrier has
43, and their exact intersection has 45 states in 24 abstract
presentations.

Array job `16686820` assigns one joint carrier state to each of 45 shards.
For every state it substitutes the exact carrier images into the 33-syllable
boundary, considers every free-product cyclic cut, appends `q^-1` in each of
the four possible target copies, and enumerates the complete noncrossing
cancellation forest relative to that carrier state.  The common classifier
then applies Q-first Tietze elimination, direct relator matching, same-root
power gcds, iterated primitive-root saturation, exact involution-root Tietze
elimination, and one relator-difference step.

All 45 jobs complete with exit code zero.  Every output contains

```text
free_nonempty_q=0
unresolved_q=0
```

Thus no carrier-and-boundary cancellation leaves a nontrivial formal target.
The normal class is globally fenced.
