---
rg: 2
id: local-syndrome-synthesis-has-an-exact-sdp-test
kind: claim
title: Joint feasible effects give an exact local-charge synthesis SDP with verifiable dual lower bounds
artifacts:
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
  - scripts/check_qpcp_syndrome_sdp.py
  - research/artifacts/qpcp-syndrome-sdp-replay-2026-09-07.json
distinct_from:
  joint-syndrome-support-characterizes-exactifiability: that characterizes recovery for a fixed measurement; this varies the joint POVM under fixed local energy bounds and supplies primal and dual certificates for synthesis.
  bounded-overlap-syndrome-energy-accounting: that sums already-supplied charges; this gives an exact finite feasibility problem for supplying compatible effects and a lower-bound certificate when proposed charges cannot hold.
---

Fix positive `h_a`, neighborhoods `N(a)`, and `A_a=sum_(b in N(a)) h_b`
on a nonzero finite-dimensional space. Let `F` be the fault sets with a
nonzero common kernel outside the set. For `C_0>=0`, an unrestricted exact
instrument with marginal effects `F_a<=C_0 A_a` exists exactly when
there are `E_S>=0` summing to `I`, with `E_S=0` for `S not in F` and
`sum_(S containing a) E_S<=C_0 A_a`.

For any `X_a>=0` and Hermitian `Y` satisfying
`sum_(a in S) X_a>=Y` for every feasible `S`, every such instrument obeys
`C_0 sum_a Tr(X_a A_a)>=Tr(Y)`. A positive trace and zero denominator
exclude all finite constants. These statements are proved without strong
duality. Neither SDP feasibility nor its generic dilation supplies physical
locality, efficient construction, or preservation of a logical algebra.

The continuation `finite-syndrome-cost-is-a-kernel-support-cone-test`
removes the prescribed constant and characterizes whether any finite one
can work. It also proves that failure always has a zero-denominator dual
certificate in this special synthesis setting; the weak-duality statement
above alone did not assert completeness of such certificates.
