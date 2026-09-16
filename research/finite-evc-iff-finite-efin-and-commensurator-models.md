---
rg: 2
id: finite-evc-iff-finite-efin-and-commensurator-models
kind: claim
title: A group has a finite E_VC model iff it has a finite E_FIN model, finitely many conjugacy orbits of commensurability classes, and finite commensurator models
distinct_from:
  finite-evc-model-restricts-to-commensurators: that claim is one direction for a single class; this claim is the two-sided characterization, whose reverse direction is the Lück–Weiermann pushout
  finite-evc-model-implies-fp-and-bvc: that claim lists consequences for G; this claim is an equivalence with conditions on commensurators
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

**Statement.** A group `G` admits a `G`-CW model for `E_VC G` with finitely many orbits of
cells if and only if all three of the following hold:

- (a) `G` admits a finite model for `E_FIN G`;
- (b) the infinite virtually cyclic subgroups fall into finitely many `G`-conjugacy orbits of
  commensurability classes (`V ~ W` iff `V ∩ W` is infinite);
- (c) for one `C` in each such orbit, the commensurator `N_G[C]` admits a finite model for the
  Lück–Weiermann family `G[C]`: finite subgroups of `N_G[C]`, and infinite virtually cyclic
  subgroups commensurable with `C`.

**Use.** A witness for `some-non-vc-group-has-a-finite-evc-model` is exactly a non-virtually-cyclic
group satisfying (a), (b) and (c). So a construction can be split into these three separate
tasks, and a candidate can be killed by showing that one commensurator fails (c).
