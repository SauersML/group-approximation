---
rg: 2
id: thompson-f-subgroup-pair-certificates-collapse
kind: claim
title: "Obstruction: Schreier-graph certificates over subgroups with a rigid interval piece, Hecke-pair and Schlichting-completion certificates, and locally finite graph actions cannot prove Thompson's group F non-amenable; the survivors are Schreier graphs over nowhere-rigid subgroups"
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that kills Schreier graphs over subgroups containing an end-rigid F[0,c] or F[c,1]; this kills every subgroup containing any F[a,b], plus the commensurated, tdlc-hull and graph-action classes, and names the exact survivors.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills finite-state expansion flows through a counting invariant; this kills subgroup-pair certificates through rigid interval subgroups with simple commutants.
  thompson-f-commensurated-subgroups-are-trivial-or-normal: that is the classification of commensurated subgroups; this is the obstruction assembled from it and from co-amenability of rigid stabilizers.
---

**ESTABLISHED** by `thompson-f-subgroup-pair-certificates-collapse-proof`, which combines
`thompson-f-commensurated-subgroups-are-trivial-or-normal` and
`thompson-f-rigid-stabilizer-schreier-graphs-are-amenable`. It decides nothing about amenability of `F`.

**The class.** A *subgroup-pair certificate* proves `F` non-amenable from one subgroup `H ≤ F` (or one action
of `F`) in one of three ways:
- (S) *Schreier:* show `Sch(F/H)` non-amenable (a Ponzi scheme, a paradoxical decomposition of `F/H`, a
  spectral gap of the quasi-regular representation on `l²(F/H)`);
- (C) *Completion:* `H` commensurated, and the Schlichting completion, or any totally disconnected locally
  compact `G` receiving `F` with dense image, shown non-amenable (sound, since a locally compact group with
  a dense amenable subgroup is amenable; standard, not re-imported);
- (G) *Graph:* an action of `F` on a connected locally finite graph whose structure forces non-amenability
  of the acting group.

**Invariant.** Rigid interval subgroups `F[a,b] ≅ F` whose commutants `F(a,b) ≅ F′` are infinite simple, and
whose conjugates exhaust `F′`.

**Where every member dies.**
- (S) dies at the *co-amenability step* whenever `H` contains some `F[a,b]`, equivalently whenever some limit
  of conjugates of `H` contains `F′`. Then `Sch(F/H)` is amenable, so no certificate can exist.
- (C) dies at the *completion step*. Every commensurated `H` is `1` or contains `F′`. So `G` is either
  discrete and equal to `F` (the certificate is the root itself) or an abelian quotient of `F`, or it is
  compact-by-abelian, hence amenable.
- (G) dies at the *stabilizer step*. Vertex stabilizers are commensurated, so either every vertex
  stabilizer is trivial (a certificate over `H = 1`, the root itself), or `F′` fixes every vertex and the
  action factors through the abelian group `F/F′ ≅ Z²`, so any implication "this action forces the acting
  group to be non-amenable" would already apply to the amenable group `F/F′`.

**Survivors (exact).** Schreier certificates over *nowhere-rigid* subgroups `H`: those containing no
`F[a,b]`, equivalently no nontrivial normal subgroup of any `F[a,b]`, equivalently whose conjugates never
accumulate on a subgroup containing `F′`. They include `H = 1`, so "some nowhere-rigid `H` has a non-amenable
Schreier graph" is equivalent to the root: the obstruction localizes every surviving (S)-certificate to
subgroups with no rigid interval piece, and every (C)- or (G)-certificate to the root itself. The
point stabilizers of `F ↷ (0,1)` are not survivors: they contain `F[0,t]`.

Proof route: `thompson-f-subgroup-pair-certificates-collapse-proof`.
