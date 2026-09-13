---
rg: 2
id: jacobson-elementary-subgroups-are-locally-finite-by-linear
kind: claim
title: Every subgroup of EL_n over a finite-field Jacobson algebra is locally finite by linear, so it contains no V and no locally finite extension of an infinite simple group
distinct_from:
  jacobson-amenable-symbol-subgroups-are-amenable: that transfers amenability through the locally finite symbol kernel; this transfers residual finiteness and excludes infinite simple sections, which is what rules out V, R^x and the Cohn group as subgroups.
  binary-jacobson-head-retaining-homomorphisms-are-faithful: that shows head-retaining homomorphisms are injective; this decides which groups can embed in EL_n(J) at all.
  cohn-elementary-group-is-not-lef: that shows EL_3 over the Cohn algebra is not LEF and contains V; this shows that group, and every group containing V, does not embed in EL_n(J).
artifacts:
  - research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md
---

**ESTABLISHED** (route `jacobson-locally-finite-by-linear-proof`; artifact Section 1). Independently re-derived by
`w4-vf-gate`: PASS, Section 31.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`.

**Statement.** Let `F` be a finite field, `J_F = F<S,T | TS=1>` and `n >= 1`. Let
`π : EL_n(J_F) -> EL_n(F[z,z^(-1)])` be the symbol map and `L_n = ker π`.
1. `L_n <= GL_fin(N x {1,...,n}, F)` is locally finite.
2. For every subgroup `H`, `H ∩ L_n` is a locally finite normal subgroup of `H`, and
   `H/(H ∩ L_n) = π(H) <= SL_n(F[z,z^(-1)])`. This quotient is residually finite.
3. A finitely generated subgroup with no nontrivial locally finite normal subgroup is residually finite.
4. No finitely generated subgroup `H` has a locally finite normal subgroup `M` with `H/M` infinite simple.

**Consequences for `E = EL_3(J)`, `J = J_(F_2)`.** `E` contains none of:
* Thompson's `V` or `T`, or any finitely generated infinite simple group;
* `R^x = L_(F_2)(1,2)^x`, which is simple (`binary-leavitt-unit-group-is-simple`);
* `EL_3(C_2)`, a locally finite extension of `R^x`;
* a finitely generated torsion-free group that is not residually finite, such as Thompson's `F`, `BS(2,3)` or
  Higman's group.

So Step 1 of the soficity question has no reduction. Every finitely generated subgroup of `E` is locally finite by
residually finite linear, which is the open amenable-by-sofic shape of `E` itself.

Every nontrivial normal subgroup of `E` contains `L` (artifact Proposition 1.4). So `E` is not residually amenable.
