---
rg: 2
id: exact-literal-e-fin-inf-switch-proof
kind: route
title: Decompose the event-cut ray into killed finite components and one possible E tail
target: exact-literal-e-fin-inf-switch
requires: []
---

Use the stagewise presentation in the target claim.  Its graph of copies of
`E` is a ray, cut at precisely the event stages.  Identity amalgamation along
each uncut edge identifies all vertex copies in that component with one copy
of `E`.  The relators at the right endpoint of every finite component kill
that copy.

Infinitely many events leave only finite components, so the presented free
product is trivial.  Finitely many events leave, in addition to the killed
finite components, exactly one unbounded component; it has no killing
relator and identity amalgamation identifies it with `E`.  Every step is
uniform because equality of the two finite enumeration snapshots at stages
`j` and `j+1` is decidable.

