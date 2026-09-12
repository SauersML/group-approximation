---
rg: 2
id: el3-z-t-no-number-field-local-host-proof
kind: route
title: Property (T) transfixes the cone markings, the finite-index subgroup lands in a product of number-field groups, and distortion forbids that
target: el3-z-t-embeds-in-no-host-with-number-field-local-groups
requires:
  - el3-of-infinite-rank-rings-not-linear-over-number-fields
  - fw-subgroups-of-eventually-similar-groups-virtually-embed
  - kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/bh-full-cantor-ca-host-2026-09-12.md
---

Notation as in the target claim. Suppose `Lambda` embeds in `G`, and identify it
with its image.

1. **FW.** By `elementary-groups-over-fg-rings-have-property-t`, `EL_n(R)` has
   property (T). Property (T) passes to finite-index subgroups, so `Lambda` has
   (T), and (T) implies FW (Delorme--Guichardet: (T) gives (FH), and FH gives FW,
   as recorded in the statement of the cited transfixing theorem).
2. **Virtual embedding into local groups.**
   - **Claim 1.** By part 1 of
     `fw-subgroups-of-eventually-similar-groups-virtually-embed`, some finite-index
     subgroup `Lambda_0 <= Lambda` embeds in a finite product
     `H_(s_1) x ... x H_(s_m)`.
   - **Claim 2.** By `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf`, some
     finite-index subgroup `Lambda_0 <= Lambda` embeds in `H^m` for some `m`. That
     theorem covers `V_(d,r)(H)` verbatim.
3. **The product is linear over `Qbar`.** If `H_(s_i) <= GL_(N_i)(Qbar)`, then
   block-diagonal placement embeds the product in `GL_M(Qbar)` with
   `M = N_1 + ... + N_m`. So `Lambda_0` is isomorphic to a subgroup of `GL_M(Qbar)`.
4. **Contradiction.** `Lambda_0` has finite index in `Lambda`, which has finite
   index in `EL_n(R)`, so `Lambda_0` is a finite-index subgroup of `EL_n(R)`. By
   `el3-of-infinite-rank-rings-not-linear-over-number-fields` it is not linear over
   `Qbar`, which contradicts step 3.

**The trivial-groupoid case without step 4.** If `H` consists of identities,
part 2 of the transfixing theorem makes `Lambda` finite. But `Lambda` contains the
infinite abelian group `Lambda ∩ E_12(R)`, which has finite index in
`E_12(R) ≅ (R, +)`.

**Topological full groups of SFT groupoids.** An element of such a full group is
given by finitely many pairs of finite paths `(u_j, v_j)` with `t(u_j) = t(v_j)`,
where the `C_(u_j)` and the `C_(v_j)` both partition the space, acting by
`u_j zeta -> v_j zeta`. For `|u| >= max_j |u_j|` it maps `C_u` onto a cone by a
canonical similarity. So it is eventually `H`-similar with `H` trivial.
