---
rg: 2
id: constant-point-sft-domains-admit-no-post-surjective-covers
kind: claim
title: No proper SFT containing a constant configuration strongly post-surjects onto the full shift
distinct_from:
  proper-sft-domains-admit-no-dual-failures: that assumes strong irreducibility and concludes pre-injectivity; this drops irreducibility and non-pre-injectivity, assumes a constant point, and concludes non-existence.
  every-group-is-dual-surjunctive: that is about automata on the whole full shift; this is about proper SFT domains with a constant point.
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that proves this statement for sofic groups (and for finite-orbit points on residually finite groups); this is the statement for all groups.
artifacts:
  - research/artifacts/constant-point-domain-count-2026-09-17.md
---

**OPEN.** Read group by group. Let `G` be a group and `A` a finite alphabet. No SFT `X ⊊ A^G` that contains
a constant configuration admits an automaton `F : X → A^G` that is strongly post-surjective with lifts inside
`X` (same alphabet on both sides).

**Why it matters.** It suffices for `gottschalk-surjunctivity-conjecture` through
`gottschalk-via-constant-point-domains`. The bounded-defect domain `X_R` of a strict pair contains the
constant `τ(a^G)`, since `τ(a^G)` is shift-fixed.

**Known cases.**
- Amenable `G`: a proper subshift has entropy `< log|A|`, and a strongly post-surjective map is onto, so
  entropy would increase. (Standard; sketched in the artifact, §4.)
- Sofic `G`: ESTABLISHED as part 2 of `proper-sft-covers-exclude-finite-orbits-and-sofic-constants`.

**How it can fail.**
- It needs a non-sofic `G` with a proper constant-point SFT and a strongly post-surjective cover.
- The compression and arrow-shift domains of `nonamenable-groups-carry-arrow-shift-strict-automata` cannot
  serve, since they have no finite orbit, hence no constant point.
- Linear sector: a one-sided inverse in `F_q[G]` gives a linear counterexample, whose domain contains `0`
  (bus lemma of `swarm-0917-w8-w8-gs-break`). So the claim at `G` forces `F_q[G]` to be stably finite.
- Whether Gottschalk at `G` implies this claim at `G` is unknown.
