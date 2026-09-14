---
rg: 2
id: kl-fp-acyclic-envelope-proof
kind: route
title: Put a finitely presented counterexample into its labelled Thompson group
target: kl-counterexample-can-be-finitely-presented-acyclic
requires: [kl-counterexample-can-be-finitely-presented, labelled-thompson-groups-are-acyclic, labelled-thompson-envelope-properties]
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

Artifact §4(a).
1. **Finitely presented counterexample.** By the first prerequisite, take a
   failure `(P, w, a)` with `P` finitely presented.
2. **The envelope `Q = V(P)`.**
   - By the third prerequisite, `iota_0 : P -> Q` is injective.
   - `Q` is of type `F_2` because `P` is, so `Q` is finitely presented; a group
     is of type `F_2` iff it is finitely presented.
   - `Q` has no proper finite-index subgroups and is strongly torsion
     generated.
   - `Q` has solvable word problem iff `P` does.
3. **Acyclicity.** The second prerequisite makes `Q` acyclic.
4. **Transfer.** The collapse identity `a = prod_j u_j w^{e_j} u_j^{-1}` in
   `P * <t>` persists in `Q * <t>`, and `a != 1` in `Q`. So `(Q, w, a)` is a
   failure. ∎
