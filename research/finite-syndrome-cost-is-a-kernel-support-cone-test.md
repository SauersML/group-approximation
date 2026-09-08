---
rg: 2
id: finite-syndrome-cost-is-a-kernel-support-cone-test
kind: claim
title: Finite local syndrome cost is equivalent to an identity resolution in feasible input support subspaces
artifacts:
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
  - scripts/check_qpcp_kernel_resolution.py
  - research/artifacts/qpcp-kernel-resolution-replay-2026-09-07.json
distinct_from:
  local-syndrome-synthesis-has-an-exact-sdp-test: that tests a prescribed constant and supplies weak dual bounds; this characterizes existence of any finite constant using only ranges and feasible labels, and proves a complete zero-denominator alternative.
  joint-syndrome-support-characterizes-exactifiability: that constrains output fault feasibility for a fixed measurement; this also restricts input effects to the ranges forced by local charges and asks whether those supports resolve the identity.
---

For fixed positive terms and energy neighborhoods, let `F` be the feasible
fault sets and `V_S=intersection_(a in S) ran(A_a)`. Some finite local
charge constant is achievable by an unrestricted exactifying instrument
if and only if `I=sum_(S in F) T_S` with `T_S>=0` supported on `V_S`.

If this fails, there are `X_a>=0` supported on `ker A_a` and Hermitian `Y`
with positive trace such that `sum_(a in S)X_a>=Y` for all feasible labels.
Their dual denominator is zero. The artifact proves this alternative
through a closed support cone and an explicit kernel-penalty construction.
Neither a span condition nor a generic frame normalization suffices.
