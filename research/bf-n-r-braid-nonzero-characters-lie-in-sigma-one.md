---
rg: 2
id: bf-n-r-braid-nonzero-characters-lie-in-sigma-one
kind: claim
title: "Every character of bF_{n,r} with a nonzero braid part lies in the BNS invariant Sigma^1"
distinct_from:
  bf-n-r-twist-invisible-braid-characters-in-sigma-infinity: that open claim asks for Sigma^infinity of the full-twist-invisible braid characters; this proved claim gives Sigma^1 for all braid-nonzero characters, including those.
---

For `n >= 2`, `r >= 1`: if `chi = pi^* psi + phi` with `phi` a nonzero
invariant braid character (`pure-braided-bht-braid-characters-dimension-n-n-minus-1`),
then `[chi]` lies in `Sigma^1(bF_{n,r})`.

The full-twist-invisible characters, for which the central-element argument is
silent, are handled by Koban–McCammond–Meier's computation of
`Sigma^1(PB_k)` (arXiv:1306.4046, Theorem A): their restrictions to the vertex
stabilizers `PB_k` are supported on many strands, so they avoid the
`P_3`- and `P_4`-circles.

Unreviewed. Proof: `research/artifacts/zp-pure-braided-bht-roots-and-sigma1-2026-09-13.md` §2.
