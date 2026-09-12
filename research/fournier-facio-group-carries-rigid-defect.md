---
rg: 2
id: fournier-facio-group-carries-rigid-defect
kind: claim
title: The Fournier--Facio group carries a rigid compression defect containing its simple factor
distinct_from:
  kun-thom-wreath-carries-rigid-defect: that computes the defect of the Kun--Thom coset wreath from a root lamp over the Theorem E pair; this computes it for the torsion-free Fournier--Facio group, where the defect contains a finitely presented simple group rather than a lamp.
  fournier-facio-torsion-free-skeleton: that records the published compression core and the simple group inside the core's defect subgroup; this identifies Gamma <= G as a rigid pair of the defect ladder, so every row DD(C) of that ladder applies to G.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.**  Let `G`, `Gamma = pi(P)`, `t_1, t_2`, `S` and
`J = t_1^-1 pi(S) t_1` be as in `fournier-facio-torsion-free-skeleton`.  Then
`Gamma <= G <= G` is a rigid pair: `Gamma` and `G` are Kazhdan, and `Gamma` is
infranormal and not normal in `G`.  Its rigid defect contains `pi(S)`:

```text
pi(S) <= D_G(G, Gamma)
       = << [g z g^-1, gamma] : g in G, z in C_G(Gamma), gamma in Gamma >>_G .
```

**Consequences for the Hilbert--Schmidt row.**

- If `hyperlinear-groups-kill-rigid-compression-defects` holds, `G` is not
  hyperlinear (`fournier-facio-nonhyperlinear-via-rigid-defect`).
- If `G` is hyperlinear, then `G` itself witnesses
  `hyperlinear-group-carries-nontrivial-rigid-defect`
  (`hyperlinear-rigid-defect-from-fournier-facio`).

So the hyperlinearity question for `G` is subordinate to the hyperlinear row
of the ladder in one direction.  A positive answer for `G` refutes that row
for every rigid configuration at once, including the Kun--Thom wreath and the
Leavitt configuration.

The pair gives no conclusion on the weakly sofic and weak MF rows, where the
ladder shows that `DD` fails.

Proof: `fournier-facio-rigid-defect-proof`.
