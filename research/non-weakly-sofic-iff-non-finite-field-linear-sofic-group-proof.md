---
rg: 2
id: non-weakly-sofic-iff-non-finite-field-linear-sofic-group-proof
kind: route
title: Linear soficity over finite fields gives weak soficity; conversely embed a finitely generated non-example in a simple group and apply the finitely generated theorem
target: non-weakly-sofic-iff-non-finite-field-linear-sofic-group
requires: [fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic, countable-group-embeds-in-two-generator-simple-group, simple-group-psl-width-is-finite-field-linear-soficity]
artifacts: [research/artifacts/fg-simple-weak-soficity-finite-field-linear-2026-09-13.md]
---

Section 4 of the artifact. "LSF" means linear sofic over finite fields.

1. **(4) => (1)** is trivial.
2. **(1) => (2).** LSF implies weakly sofic. `GL_n(F_q)` is finite and the normalized rank length is bi-invariant, so
   an LSF embedding is an embedding into a metric ultraproduct of finite groups with invariant lengths (definition
   bullet on `simple-group-psl-width-is-finite-field-linear-soficity`). So a non-weakly-sofic group is not LSF.
3. **(2) => (3).**
   - *Locality.* A countable group all of whose finitely generated subgroups are LSF is LSF. Enumerate the group as an
     increasing union of finitely generated subgroups, take for each an approximation that is rank-almost multiplicative
     and separating on a finite window, and diagonalize along a nonprincipal ultrafilter. So a non-LSF countable group
     has a finitely generated non-LSF subgroup `Gamma_0`.
   - *Envelope.* By `countable-group-embeds-in-two-generator-simple-group` (Schupp), `Gamma_0` embeds in a
     two-generator simple group `S`. LSF passes to subgroups, so `S` is not LSF.
4. **(3) => (4).** By `fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic`, a finitely generated simple weakly
   sofic group is LSF. So `S` is not weakly sofic.
