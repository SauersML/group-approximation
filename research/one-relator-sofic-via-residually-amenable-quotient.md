---
rg: 2
id: one-relator-sofic-via-residually-amenable-quotient
kind: route
title: Answer Pestov 4.10 from a sofic radical and a residually amenable quotient
target: one-relator-groups-sofic
requires: []
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

The shortcut that would nearly collapse the whole question, and the most
attractive wrong turn in this region.

Linton's Theorem 1.1 gives `R = G_Q^(ω) = <<r>>_G` with `G/R = F/<<r>>`
**residually rationally solvable**, hence residually solvable, hence residually
amenable.  So if an extension with sofic kernel and residually amenable quotient
were sofic, then soficity of the radical `R` ([[linton-radical-sofic]]) would
immediately give soficity of `G` — no shell, no action hypothesis, no Magnus
chain.  Pestov's Question 4.10 would reduce, in one line, to a statement about
normally-one-generated rationally perfect groups.

**Dead: the extension theorem is withdrawn.**  Its only source is
Ji--Ogle--Ramsey, *Relative Amenability and Relative Soficity*
(arXiv:1807.07600), and the arXiv record carries the comment "Error in proof of
Theorem 3.15"; see [[relative-soficity-extension-theorem-withdrawn]], where the
transcription and the withdrawal history are recorded.

## The distinction this route exists to preserve

Being killed by a **withdrawal** is not the same as being killed by a
**refutation**.  Nothing here shows the extension statement is false — no
counterexample to it is known — so this route is unsupported rather than
excluded, and proving the statement would be a real theorem that revives the
route.  Compare `linton-shell-sofic-via-generic-semidirect-closure`, which is
dead in the stronger sense: its permanence property has explicit
counterexamples.  A reader who conflates the two will either over-report what is
open or waste effort looking for a counterexample that may not exist.

## Where the amenability that does work is used

The genuinely amenable quotient is the finite-stage one.  `G/G_Q^(n)` is
solvable, not merely residually so, and Elek--Szabó applies unconditionally —
which is exactly why
[[one-relator-soficity-localizes-at-rational-derived-stage]] stops at `E` and
not at `R`.  The last step, from the finite stage down to the transfinite one, is
the step this withdrawn theorem would have supplied and nothing else does.

Fox--Magnus descent now gives a different, valid quotient:
[[one-relator-fox-magnus-descent-to-derived-linton-radical]] embeds `G/R'` in
a sofic wreath product and makes `E/R'` residually finite.  That advance does
not revive this route: these quotients are sofic or residually finite, not
amenable in general, so the only extension permanence available here still
does not apply.
