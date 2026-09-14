---
rg: 2
id: short-towers-force-large-lef-models
kind: claim
title: A clopen set with no returns up to 2m and transvections of length κ forces LEF models of order 2^{Θ(m²)} at radius 20κ + 480m
---

**Statement.** Let X be an infinite minimal subshift, G_X = EL_3(LC(X,F_2)⋊Z) with the generators
{e_ij(s) : s ∈ {1, u^{±1}, e_a}}, and let L_X(r) be the LEF growth (Bradford).

Let W ⊆ X be a nonempty clopen set with W ∩ T^tW = ∅ for 0 < |t| ≤ 2m, and let κ = max_{i≠j} |e_ij(e_W)|. Put d = 3(2m+1). Then

`L_X(r) ≥ 2^{d(d−1)/2}` for every `r ≥ 20κ + 480m`.

**Mechanism.**
- The tower over W carries a copy of GL_d(F_2) whose elementary transvections have length ≤ 4(κ + 24m).
- In any finite model of B(r), their images satisfy the defining relations of U_d(F_2), and the central transvection stays nontrivial.
- A nontrivial normal subgroup of the 2-group U_d(F_2) meets its centre, so U_d(F_2) embeds in the model.

This is Theorem C of `research/artifacts/sk-lef-growth-bounds-2026-09-13-part2.md` (§4–5), extracted as its own node so that other tower constructions can consume it.

**Status: established** by `short-towers-force-large-lef-models-proof`. UNREVIEWED; queued with sk-referee-2 (it is also inside the Sturmian route already queued there).
