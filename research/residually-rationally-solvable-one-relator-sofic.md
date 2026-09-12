---
rg: 2
id: residually-rationally-solvable-one-relator-sofic
kind: claim
title: Every residually rationally solvable one-relator group is sofic
distinct_from:
  one-relator-soficity-localizes-at-rational-derived-stage: that is the reduction available for *every* one-relator group and decides nothing; this is the outright positive answer on the subclass where the reduction's shell is free, and it closes those groups.
  one-relator-groups-sofic: that is Pestov's Question 4.10 in full and is open; this settles it on a proper subclass, and the residual hypothesis is exactly what a counterexample must fail.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

ESTABLISHED.  If a one-relator group `G = F/<<w>>` is **residually rationally
solvable** — that is, `G_Q^(ω) = 1` — then `G` is sofic.

## Proof

By Linton's Corollary 1.2 (arXiv:2407.09272), residual rational solvability of
a one-relator group is equivalent to `E := G_Q^(n)` being **free** for some
finite `n`, and his proof gives `n <= |w|`.  Free groups are sofic.  By
[[one-relator-soficity-localizes-at-rational-derived-stage]](1), `G/E` is
solvable and hence amenable.  Sofic kernel plus amenable quotient gives `G`
sofic (Elek--Szabó).  ∎

## Why this is worth a node

It is a genuinely large positive class, and it is the *cleanest* thing the
2026-08-17 external attempt on Question 4.10 produced.  The class contains every
free group, every one-relator group with solvable rational derived series
(so all the classical residually-solvable families), and every surface group;
`[a,b]` gives `E = [S,S]`, free because infinite-index subgroups of surface
groups are free.

It also sets the frontier precisely.  A nonsofic one-relator group has to fail
this hypothesis, so its Linton radical `R = G_Q^(ω) = <<r>>_G` is nontrivial —
and Linton shows a nontrivial radical in the torsion-free case is infinitely
generated.  That is exactly the regime in which the one automatic criterion for
sofic actions by automorphisms (Alekseev--Bradford, for finitely generated
residually finite targets) does not apply, which is why
[[linton-shell-sofic]] is hard rather than routine.

## Scope note

"Residually rationally solvable" is strictly stronger than "residually
solvable": the series here is the *rational* derived series, whose successive
quotients are torsion-free abelian.  Koch-Hyde--O'Connor--Olive
(arXiv:2606.13933) supply further one-relator families that are residually
solvable; each of them lands in this class only when its witnessing series can
be taken rational, and the node does not claim otherwise.
