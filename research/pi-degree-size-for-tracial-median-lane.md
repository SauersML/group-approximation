---
rg: 2
id: pi-degree-size-for-tracial-median-lane
kind: claim
title: A PI-degree-weighted observable is the refinement-robust size the block-decomposition lane needs
distinct_from:
  tracial-median-concentration: that concentrates the trace-median block observable and is blocked because the trace is refinement-blind; this proposes replacing the median statistic by a polynomial-identity-degree-weighted observable that the trace-blindness obstruction cannot touch.
  invariant-size-collapse: that is the exact algebraic invariant-size-makes-compression-equality statement; this seeks the approximate quantitative substitute using PI degree rather than trace.
  rectangular-escape: that is the Fanizza-lane countermodel where trace-equal source/target packets have different matrix-factor degree; this imports its lesson (PI degree is the amplification-proof discriminator) into the Leavitt block lane.
---

Both the Leavitt block-decomposition lane
(`tracial-median-concentration`, `hs-expander-block-decomposition`)
and the Fanizza whole-map lane (`rectangular-escape`) are blocked by
ONE obstruction: the normalized trace is refinement-blind, so a proper
compression can be masked by external multiplicity refilling the lost
rank (`M_r` traded for `M_r tensor M_m` at equal trace).  The Fanizza
lane already isolated the amplification-proof discriminator that trace
cannot see: the standard polynomial `s_(2r)` vanishes identically on
`M_r tensor I_m` for every `m` but not on `M_(r+1)`
(Amitsur--Levitzki), so PI DEGREE is a conjugation-invariant,
multiplicity-robust size of a matrix block.

CLAIM (proposal, with its own falsification gate below): the
block-size observable that `tracial-median-concentration` needs — the
one the permutation argument gets for free from Hamming cardinality
but the trace cannot supply — is realized by a PI-degree-weighted
functional

```text
sigma(p) = sup { r : s_(2r) does not vanish to o(1) on p M_d p },
```

which, unlike the trace, is strictly monotone under proper compression
and stable under the `X -> X tensor I_m` amplification firewall.
Substituting `sigma` for the trace-median `M` in the concentration
statistic would make the fine blocks asymptotically equal in
PI-degree inside each coarse block, which is the equitraciality output
the lane consumes — but now via a size the rectangular escape cannot
counterfeit.

## Attempts

- **Why this is not immediately the answer (honest gate).**  PI degree
  is conjugation-invariant, hence ALSO invariant under the unitary
  compressors `u, v` themselves, so it does not by itself detect the
  properness of `u Gamma u^(-1) <= Gamma`; the detection must come
  from the compressor being NON-unitary on the recovered corner
  (`u` implements a proper corner inclusion of the ambient algebra,
  not a global conjugation), where PI degree genuinely drops.  The
  precise question is therefore whether the recovered
  block algebra's PI degree, read along the nested Leavitt corner
  chain, strictly decreases per level with an amplification-proof gap
  — the exact analogue of the Fanizza "charge the label/multiplicity
  conversion" obligation, imported to the Leavitt corners.
- **Falsification.**  If the nine-leaf Leavitt corner inclusion
  (`openai-nine-leaf-leavitt-configuration`) can be realized with the
  recovered corner PI-degree CONSTANT along the chain (a rectangular
  refilling internal to the Leavitt corner), the PI observable is as
  blind here as the trace and the proposal dies — the same test that
  `rectangular-escape` applies in the Fanizza lane, run on the
  Leavitt corner triple.  This is the one computation that decides the
  proposal, and it is finite at each fixed corner level.
