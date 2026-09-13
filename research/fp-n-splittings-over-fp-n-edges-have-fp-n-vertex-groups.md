---
rg: 2
id: fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups
kind: claim
title: "If a group of type FP_n splits as a finite graph of groups with edge groups of type FP_n, every vertex group is of type FP_n"
invalidates:
  - type-fn-hosts-via-vertex-groups-over-fp-edges
distinct_from:
  higman-rope-trick-group-is-never-fp3: that computes H_3 of one specific HNN container whose edge group is not of type FP_2; this is a general permanence theorem for splittings whose edge groups are of type FP_n
---

Let `H` be the fundamental group of a finite graph of groups with vertex groups
`G_v` and edge groups `G_e`. Suppose `H` is of type `FP_n` and every `G_e` is
of type `FP_n`. Then every `G_v` is of type `FP_n`, and so is every retract
of every `G_v`.

**Consequence for Zaremsky Problem 1.1.** Let `G` be of type `F_n` and not of
type `F_{n+1}`, with `n >= 2`. Then `G` is finitely presented and not of type
`FP_{n+1}`, because finitely presented plus `FP_{n+1}` gives `F_{n+1}`
(Fournier-Facio--Zaremsky arXiv:2607.21727v1, Lemma 2.1). So no host of type
`F_{n+1}` splits over edge groups of type `FP_{n+1}` (for instance free
groups, or groups of type `F_∞`) with `G` as a factor or retract of a vertex
group. A splitting host needs edge groups that fail `FP_{n+1}` in a way that
cancels the defect of the vertex groups. The rope trick does exactly this at
level 2: its edge group, the double `F *_R F`, is not of type `FP_2`.

Proof: `fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups-proof`.
