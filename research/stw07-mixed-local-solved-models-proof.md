---
rg: 2
id: stw07-mixed-local-solved-models-proof
kind: route
title: Apply Gabe or the faithful-trace UCT theorem locally and then use norm locality
target: stw07-mixed-local-solved-models-are-qd
requires:
  - stw07-local-qd-subalgebras-force-quasidiagonality
---

Every C*-subalgebra `B` of `A` is exact and stably finite: exactness passes
to subalgebras of the nuclear algebra `A`, and stable finiteness passes to
subalgebras.

For a local model of type 1, Gabe's traceless theorem applies to the
separable exact stably finite algebra `B` and makes it AF-embeddable, hence
quasidiagonal.  For a model of type 2, nuclearity makes its faithful trace
amenable, and the faithful-trace UCT theorem of
Tikuisis--White--Winter/Schafhauser makes `B` AF-embeddable, hence
quasidiagonal.  Thus every finite subset of `A` is approximated by a
quasidiagonal unital subalgebra.  The norm-local quasidiagonality theorem
finishes the proof.
