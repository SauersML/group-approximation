---
rg: 2
id: surjunctive-groups-carry-invisible-rigid-defects
kind: claim
title: Rigid compression defects are sofic-invisible and occur nontrivially in surjunctive groups
distinct_from:
  kt-lef-graph-wreaths-surjunctive-and-nonsofic: that proves the Kun--Thom graph wreaths surjunctive and nonsofic; this places their rigid defect in the sofic radical and reads it against Garden-of-Eden localization, showing a window on that defect yields no strict pair.
  sofic-radical-localizes-garden-of-eden-windows: that is the necessary condition that every Garden-of-Eden window contains an invisible difference; this shows the compression mechanism's canonical invisible element satisfies it inside groups that carry no strict pair.
  sofic-groups-kill-rigid-compression-defects: that kills rigid defects inside sofic ambient groups; this applies it to images in metric ultraproducts, putting every rigid defect of any group in its sofic radical.
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

**ESTABLISHED** by `surjunctive-invisible-rigid-defects-proof`.

1. **Invisibility.** Let `Gamma <= G <= H` be a rigid pair: `Gamma` and `G` Kazhdan,
   and `Gamma` infranormal in `G`. Every rigid defect `[t z t^-1, gamma]`, with `t in G`,
   `z in C_H(Gamma)` and `gamma in Gamma`, lies in the sofic radical `Rad(H)`.
2. **Surjunctive carriers.** Take a Kun--Thom Theorem E pair `Gamma < G`, and put
   `W = (Z/2) wr_(G/Gamma) G`. Take a strict compressor `t`, and `gamma` in `Gamma`
   outside `t Gamma t^-1`. Then `d = [t a_Gamma t^-1, gamma] = a_(t Gamma) a_(gamma t Gamma)`
   is a nontrivial rigid defect, and `W` is surjunctive. The same holds for every
   Kun--Thom graph wreath with a nontrivial LEF lamp.
3. **Table filter.** No strict pair over any group has window data realizable in such a
   group with the distinguished window cells kept apart.

**Reading for designs.** Placing a Garden-of-Eden window on a rigid defect `{1, d}` meets
the necessary condition of `sofic-radical-localizes-garden-of-eden-windows`, and it
still gives no strict pair.
- Every relation of the configuration holds in `W` with `d != 1`: a Kazhdan `Gamma` in a
  Kazhdan `G`, a strict compressor, and a centralizing involution.
- A defect-window certificate must therefore use a product-table coincidence that fails
  in every Kun--Thom graph wreath once the window pair is separated.
- The defects here are not nested (`t a_Gamma t^-1` is a lamp, outside `G`); see
  `nested-rigid-defects-force-nonsurjunctivity` for the nested case.

Proof: Sections 2 and 3 of the linked artifact.
