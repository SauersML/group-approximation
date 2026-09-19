---
rg: 2
id: rational-perfect-core-blocks-rrs-kernel-lifts
kind: claim
title: A rationally perfect core is invisible in every over-quotient lift with residually rationally solvable kernel
distinct_from:
  perfect-mf-reflection-over-residually-p-actor: that starts with an MF-invisible perfect kernel and identifies several residuals when the quotient is residually-p; this starts with a rationally perfect kernel and proves its invisibility in every exact lift whose new kernel is residually rationally solvable, with no MF or residually-p hypothesis.
  leavitt-degree-kernel-quotient-tests-are-procyclic: that computes finite and solvable images of one specific free-product degree kernel; this is a general functorial statement about any rationally perfect core sitting over a fixed quotient.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that positively constructs the maximal first-order finite-torsion lamp quotient; this negatively rules out all higher exact lifts over the canonical quotient whose kernel remains residually rationally solvable.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `R` be a rationally perfect normal subgroup of `G`, put `H=G/R`, and let
`pi:G->H` be the quotient.  Suppose

    Phi : G -> P,          q : P -> H,          q Phi = pi.

If `ker(q)` is residually rationally solvable, then `Phi(R)=1`.

If `R` is perfect, the same conclusion holds under the weaker assumption that
`ker(q)` is residually solvable.  Consequently, the short marker supplied by
[[linton-radical-has-a-short-weinbaum-marker]] cannot be recovered from the
canonical Linton quotient by any exact tower of rational-solvable kernel
extensions; in the perfect case no exact prosolvable-kernel lift can recover
it either.
