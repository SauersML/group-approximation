---
rg: 2
id: higman-collapse-via-trivially-padded-bs-correction
kind: route
title: Correct each BS seam after identity padding, then collapse the glued exact cycle
target: higman-four-cycle-intrinsic-mf-seed
requires:
  - higman-seam-gate-needs-only-padded-bs-correction
  - bs12-trivially-padded-opnorm-correction
  - higman-exact-packet-cycles-collapse-opnorm
---

Item 1 of `higman-seam-gate-needs-only-padded-bs-correction` is exactly the
implication `(TPC)+(CGC) => (HMF5)`.  Here `(TPC)` is
`bs12-trivially-padded-opnorm-correction` and `(CGC)` is
`higman-exact-packet-cycles-collapse-opnorm`.  `(HMF5)` is the uniform form of
`(HMF2)=>(HMF3)` in `higman-four-cycle-intrinsic-mf-seed`, as that claim
records.

This replaces the gate's first statement (same-dimension correction, an open
Eilers--Shulman--Sorensen question) with the weaker identity-padded
correction.  The two prerequisites can fail independently.  `(TPC)` is a
`BS(1,2)` statement, and it can fail while the Higman collapse holds.
`(CGC)` is equivalent to the target given `(TPC)`, so it carries the entire
Higman content.  Per-seam corrections with nontrivial auxiliaries (Willett's
`R_q`-padding) do not supply `(TPC)`, by item 4 of the reduction claim.
