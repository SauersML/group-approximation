---
rg: 2
id: magnus-piece-meets-linton-radical-proof
kind: route
title: A radical missing every piece acts freely on the Magnus tree and is rationally perfect
target: magnus-piece-meets-nontrivial-linton-radical
requires: [linton-radical-abelianization-is-truncated-group-ring]
---

**1.** `G` is the HNN extension of `B_0` identifying `F_-` with `F_+`, so `G` acts
without inversions on its Bass--Serre tree, and the vertex stabilizers are the
conjugates of `B_0`. Suppose `R ∩ g B_0 g^(-1) = 1` for every `g`. Then `R` acts
freely, so `R` is free. The prerequisite gives `R_ab ≅ (Z/kZ)[G/R]`, a torsion
group, so `H_1(R;Q) = 0`. A free group with trivial rational abelianization is
trivial, contradicting `R != 1`. So `R ∩ g B_0 g^(-1) != 1` for some `g`, and
conjugating by `g^(-1)` gives `R ∩ B_0 != 1`, since `R` is normal.

**2.** The rational derived series is functorial. If `x in G_Q^(i+1)`, then
`x^m in [G_Q^(i), G_Q^(i)]` for some `m >= 1`, so `rho(x)^m in [H_Q^(i), H_Q^(i)]`.
By induction `rho(G_Q^(i)) <= H_Q^(i)` for every `i`, and so
`rho(R) <= H_Q^(omega) = 1`.

Free groups and residually torsion-free nilpotent groups have trivial
`H_Q^(omega)`, because their lower central quotients are torsion-free.
