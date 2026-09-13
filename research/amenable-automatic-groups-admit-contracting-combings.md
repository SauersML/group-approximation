---
rg: 2
id: amenable-automatic-groups-admit-contracting-combings
kind: claim
title: Every amenable automatic group admits a contracting combing
distinct_from:
  contracting-combings-give-contractible-rips-complexes: that is Alonso's established theorem that contracting combings give contractible Rips complexes; this is the open claim that amenable automatic groups have such combings
  amenable-automatic-groups-have-contractible-rips-complexes: that is the affirmative answer to Zaremsky Problem 4.1; this is a combing statement that implies it through Alonso's theorem
---

**OPEN.** Every amenable automatic group `G` has a finite generating set whose word
metric admits a contracting combing in Alonso's sense (definition in
`contracting-combings-give-contractible-rips-complexes`).

With Alonso's theorem this gives
`amenable-automatic-groups-have-contractible-rips-complexes` (route
`amenable-automatic-rips-via-contracting-combings`).

## Attempts

- 2026-09-13 (lane z4-01-amen-auto-rips): an automatic structure gives a bounded
  combing with linear `φ(n) = Cn + D` (Zaremsky, arXiv:1812.10976v3, after
  Citation 6.7). The contracting condition says that stepping `⌊C/2⌋` back along one
  combing line keeps it `C`-close to a later point of another. That is hyperbolic-type
  control, and linear fellow travelling does not give it. Hyperbolic groups have
  contracting combings.
- Virtually abelian groups: no contracting combing is recorded. Zaremsky writes in
  1812.10976v3 (after Theorem 6.5) that he was then "not even sure whether `Z^n` with
  the standard word metric admits a contractible proper Vietoris–Rips complexes for
  all n". Their contractible Rips complexes in this graph come from dominated-vertex
  collapses, not combings (`linf-preserving-proper-actions-give-contractible-rips`).
  So this route may be strictly stronger than needed.
