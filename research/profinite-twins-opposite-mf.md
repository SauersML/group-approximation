---
rg: 2
id: profinite-twins-opposite-mf
kind: claim
title: Profinite twins with opposite MF behaviour
distinct_from:
  compression-wreath-five-radicals-coincide: That identifies one kernel with five residuals of a single group; this compares two different groups and shows the whole finite-index and profinite theory cannot separate them while MF does.
  continuum-nonisomorphic-fg-non-mf: That is a cardinality statement about isomorphism types of non-MF groups, witnessed by direct products `E x N_i`; this is a two-group statement in which one member is MF and the other is not, with matching profinite data.
artifacts:
  - GroupApproximation/Algebra/VisibleQuotient.lean
  - GroupApproximation/Sofic/ProfiniteTwins.lean
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
---

Let `K` be a nontrivial finite **perfect** group, for instance `A_5`, and let

    W_K = K^(G*/Gamma*) x| G*.

Then `K_ab = 1`, the telescope kernel is the entire lamp base, and the split
projection `W_K ->> G*` has the following simultaneous properties.

- `G*` is residually finite, linear over `Z[1/2]`, and MF; `W_K` is sofic and
  **not** MF, and not residually finite.
- The projection induces an isomorphism of profinite completions
  `hat(W_K) = hat(G*)`, and an isomorphism of Bohr compactifications.
- It induces an inclusion- and index-preserving bijection between **all**
  finite-index subgroups, normal or not, namely `M |-> K^(G*/Gamma*) x| M`,
  hence identical subgroup-growth sequences.
- It induces an equivalence of the categories of finite actions, and of
  finite-dimensional representations over every field (objects and
  intertwiners).
- Both the projection and its canonical section `G* -> W_K` are inverse
  bijections on Hom-sets into every one of those target classes.

So MF is not determined by the profinite completion among finitely generated
groups, and the restricted family of finite, compact, linear, and matricial
targets is not jointly conservative: it sends a non-injective split
epimorphism to a bijection on every Hom-set it can see.

The mechanism is machine-checked in `Sofic/ProfiniteTwins`: precomposition with
the quotient map is a bijection on homomorphisms into every finite group, as
soon as the collapsed subgroup lies in the finite residual.  `wreath_twins`
instantiates it on the ascending-HNN wreath product against its first-stage
quotient ([[stage-one-lamp-difference-radical]]), where the separating subgroup
is nontrivial and the non-MF side is unconditional.  The perfect-lamp version
above still needs the telescope radical to be identified with the whole lamp
base.
