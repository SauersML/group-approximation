---
rg: 2
id: brick-af-cocycle-referee-confirmation
kind: claim
title: "The brick groupoid Z^n-cocycle with AF kernel survives a referee pass of its own, cast on that claim alone and not inside a batch"
distinct_from:
  brick-groupoid-has-zn-cocycle-with-af-kernel: that is the mathematical statement about the cocycle and its AF kernel; this is the procedural referee gap that keeps its proof route from deriving it, opened because the claim was voted on inside a batch whose other half was refuted.
  af-by-zk-full-groups-have-finite-kazhdan-subgroups: that is the general statement (S_k) about full groups of AF-by-Z^k groupoids, which is genuine open mathematics; this asks for no new mathematics at all, only a per-claim vote.
  kazhdan-host-crossed-product-is-simple-and-nuclear: that is a substantive import gap in the O_2 computation, found by a referee; this is a procedural gap in a different claim of the same batch, in which no referee found a defect.
artifacts: []
---

**Status: OPEN.** On 2026-09-18 the batch landing of
`brin-thompson-groups-nv-are-a-t-menable` posted two claims at once,
`nv-brick-groupoid-and-kazhdan-host-are-both-o2` and
`brick-groupoid-has-zn-cocycle-with-af-kernel`, and two of three referees voted refuted.
**Neither refutation touched the cocycle claim.** All three lenses checked it
independently and found it correct:

- `ker c = {(x,0,y)}` forces `k = l`, so the kernel is exactly equal-level tail
  equivalence (lens 1, lens 2, lens 3);
- `R_k = ⋃_{|μ|=|ν|=k} U_{μ,ν}` is compact open, principal, with orbits of constant size
  `2^k`, hence elementary, and `R_k^n` increases to `R_2^n` (lens 1, lens 2);
- products of AF groupoids are AF, and the C*-side cross-check (the UHF core
  `M_{2^∞}^{⊗n}` as the `T^n`-gauge fixed-point algebra) is consistent (lens 1);
- lens 2 recorded the node and its proof as "clean and import-free".

**Claim.** The route `brick-groupoid-zn-cocycle-af-kernel-proof` passes a referee pass
whose scope is that claim alone.

Once such a pass is recorded, drop this requirement from
`brick-groupoid-zn-cocycle-af-kernel-proof` and the target returns to ESTABLISHED. No
step of the route is expected to change.

## Attempts

- **2026-09-18, batch referee pass.** Three lenses checked the cocycle claim inside a
  batch vote and found each step correct. **Where it stops:** the votes were cast on the
  batch, which was refuted because of the O_2 computation (lens 2: the
  Rørdam–Sierakowski quantifier inversion, now
  `kazhdan-host-crossed-product-is-simple-and-nuclear`) and because of the gate wording
  on the target node (lens 3). A per-claim vote on the cocycle has not been recorded.
