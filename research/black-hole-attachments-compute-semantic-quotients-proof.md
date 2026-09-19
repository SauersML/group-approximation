---
rg: 2
id: black-hole-attachments-compute-semantic-quotients-proof
kind: route
title: Restrict to the visible vertex and use triviality on every attached black hole
target: black-hole-attachments-compute-semantic-quotients
requires:
  - universal-mf-quotient
---

Let `f:A(B,C;G)->M`, where `M` is MF.  Full MF radical makes the restriction
`f|_B` trivial.  Agreement on the amalgamated subgroup therefore forces
`f|_G` to kill `i(C)`, hence its normal closure.  Thus restriction gives a
map

```text
Hom(A(B,C;G),M)->Hom(barG,M).
```

Conversely, a map `barG->M` gives a map `G->M` which kills `i(C)`.  This map
and the trivial map `B->M` agree on `C`, so the amalgam universal property
extends them uniquely to `A(B,C;G)`.  The two constructions are inverse and
natural, proving `(BHA1)`.

The universal property of MF reflection now gives `(BHA2)`.  If `barG` is
MF, the displayed map to `barG` itself detects every element outside its
kernel, while `(BHA1)` says that every MF-target map kills the kernel.  This
proves `(BHA3)`.

If `C=<c>` and `c` normally generates `B`, then quotienting the amalgam by
the normal closure of `c` kills all of `B` and kills `i(C)` in `G`, leaving
exactly `barG`.  Hence the radical in `(BHA3)` is `normalClosure(c)`.  The
normal-form theorem embeds both vertices and keeps `c` nonidentity.

For a family of attachments, repeat the same restriction argument: every
attached `B_j` maps trivially, so the `G`-map kills every `i_j(C_j)`; the
converse extension follows from the universal property of the iterated
amalgam.  This proves `(BHA4)`.  The finite-presentation assertion is the
standard presentation of a finite amalgam of finitely presented vertex
groups over finitely generated edge groups.
