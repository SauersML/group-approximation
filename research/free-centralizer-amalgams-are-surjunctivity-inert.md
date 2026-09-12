---
rg: 2
id: free-centralizer-amalgams-are-surjunctivity-inert
kind: claim
title: Adjoining a free LEF centralizing factor over any subgroup preserves surjunctivity in both directions and creates nontrivial compression defects
distinct_from:
  lef-lamp-graph-wreaths-are-surjunctive: that is the permanence theorem for graph wreaths over a surjunctive actor; this identifies the amalgam of an arbitrary host with a centralizing factor as the empty-graph wreath, and reads the result as inertness of defect windows built from a free commuting factor.
  graph-folds-over-surjunctive-groups-are-surjunctive: that needs a homomorphism into a surjunctive group injective on vertex groups; this needs no surjunctive target and gives an equivalence with the host, including hosts such as the Leavitt unit group that lie outside every permanence closure.
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

**ESTABLISHED** by `free-centralizer-amalgam-inertness-proof`.

Let `H` be any group, `Gamma <= H` any subgroup, and `K` any group. Put
`P = H *_Gamma (Gamma x K)` and `X = H/Gamma`.

1. `P ≅ Lambda(K) ⋊ H`. Here `Lambda(K)` is the free product of copies `K_x`,
   `x in X`, and `h k_x h^-1 = k_(h x)`.
2. If `K` is LEF, then `P` is surjunctive iff `H` is surjunctive.
3. Let `t in H` satisfy `t Gamma t^-1 < Gamma`, let `gamma in Gamma` lie outside
   `t Gamma t^-1`, and let `k in K` be nontrivial. Then
   `[t k t^-1, gamma] = k_(t Gamma) (k^-1)_(gamma t Gamma) != 1`. When
   `Gamma <= <P_Gamma>` is a rigid pair, this defect lies in the sofic radical of `P`.

**Consequence.**
- **No strictness either way.** Defect windows on a free centralizing factor neither
  create nor destroy strict pairs: `P` carries one iff `H` does.
- **Leavitt instance.** For `H = L_(F_2)(1,2)^x` with the nine-leaf pair, those windows
  are exactly as hard as Gottschalk's conjecture for `H`.
- **What a certificate must use.** The relations "`k` commutes with `Gamma`" and
  "`t Gamma t^-1 <= Gamma`" carry no strictness. A defect-window certificate needs
  relations tying the commuting factor into the host, as in
  `nested-rigid-defects-force-nonsurjunctivity`.

Proof: Section 4 of the linked artifact.
