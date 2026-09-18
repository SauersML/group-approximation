---
rg: 2
id: substitution-subshift-full-groups-satisfy-boone-higman-proof
kind: route
title: Stationary Bratteli--Vershik model, then the Vershik map in a contracting RSG, then the BBMZ host
target: substitution-subshift-full-groups-satisfy-boone-higman
requires:
  - substitution-subshifts-have-stationary-bv-models
  - stationary-vershik-maps-generate-contracting-rsgs
  - contracting-rsgs-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

1. **Model.** By `substitution-subshifts-have-stationary-bv-models`,
   `(X_tau, S)` is isomorphic to the Vershik system `(E, T)` of a stationary
   properly ordered diagram with simple top edges. Its read substitution `sigma` is
   primitive, has all images of length `>= 2`, and has constant first letter `l` and
   last letter `r`. An isomorphism of Cantor systems induces an isomorphism of
   topological full groups, so `[[S]] ≅ [[T]]`.
2. **Coding.** That diagram is exactly the graph `Gamma` of
   `stationary-vershik-maps-generate-contracting-rsgs`: nodes `A ⊔ {rho}`, the edges
   between levels given by `sigma`, and `E = C_rho`. By that claim,
   `G_0 = <V_{Gamma,E}, T>` is an RSG with finite nucleus `N = Nuc_{G_0}`.
3. **Full closure.** By the "Consequence" of
   `contracting-rsgs-embed-in-fp-simple-groups` (BBMZ Prop. `NucleusHasProperties`
   and Thm `RSGCharacterization`), `G_N = {f ∈ R_{Gamma,E} : Nuc_f ⊆ N}` is a full
   contracting RSG containing `G_0`. Every `h ∈ [[T]]` agrees near each point with
   some power `T^n ∈ G_0`, so `h` locally agrees with `G_0`, and since `G_N` is full,
   `h ∈ G_N`. So `[[T]] <= G_N`.
4. **Host.** BBMZ Prop. `contr_to_simple` embeds `G_N` in the finitely presented
   simple twisted Brin--Thompson group `SV_{G_N}`. Composing, `[[S]] ≅ [[T]] <= G_N
   <= SV_{G_N}`.

Subgroups inherit the embedding, which gives the consequences in the target.
