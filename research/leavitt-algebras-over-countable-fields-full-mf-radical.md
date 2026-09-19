---
rg: 2
id: leavitt-algebras-over-countable-fields-full-mf-radical
kind: claim
title: Elementary groups of every Leavitt algebra L_k(1,m) over a countable field have full MF radical from rank four
distinct_from:
  binary-leavitt-all-ranks-full-mf-radical: that is `k = F_2`, `m = 2`, at every rank including one to three, through the rank-twelve headline; this is every countable field and every `m ≥ 2`, from rank four, through the ring criterion alone, with no simplicity, exchange-ring, centre, or `GL = EL` input.
  full-complementary-idempotent-elementary-full-mf-radical: that is the ring criterion; this is its instance at the Leavitt algebras, where the defining relations verify the criterion directly.
  generic-leavitt-self-compression-full-mf-radical: that assumes property (T) of `E_4` and `E_n` and rank at least sixteen; this needs neither, so it covers infinite fields, where the elementary groups need not be finitely generated or Kazhdan.
artifacts:
  - non_mf_groups_exist.tex
---

Let `k` be a countable field, `m ≥ 2`, and `R = L_k(1,m)` with generators
`s_1, …, s_m, t_1, …, t_m`, `t_i s_j = δ_{ij}`, `Σ s_i t_i = 1`.  Then for
every `n ≥ 4` every homomorphism from `EL_n(R)` to an MF group is trivial.

For finite `k` these groups are finitely generated Kazhdan groups; for
infinite `k` the conclusion holds without either property, by the
finitely-generated-subring exhaustion inside the criterion.  Printed as the
second half of `cor:simple-infinite-ring`.
