# PI-degree size proposal for the tracial-median lane

**Archived 2026-08-21.** This is a preserved research proposal, not an active
Cairn claim. It currently has no proved implication into the live graph.

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

## The finite-dimensional Leavitt obstruction is the real engine

By hand: `L_(F_2)(1,2)` has isometries `s_1, s_2` with
`s_i^* s_i = 1` and `s_1 s_1^* + s_2 s_2^* = 1`.  No nonzero
finite-dimensional `*`-representation exists — an isometry of a
finite-dimensional Hilbert space is a unitary, so `s_i s_i^* = 1`,
forcing `1 + 1 = 1`.  Hence in any `delta`-almost representation the
Leavitt defect `|| s_1 s_1^* + s_2 s_2^* - 1 ||_2` competes with the
isometry defects `|| s_i^* s_i - 1 ||_2`, and a normalized-HS count
gives the EXACT budget

```text
|| s_1 s_1^* + s_2 s_2^* - 1 ||_2 >= (something) - trace slack,
```

because `tau(s_i s_i^*) = tau(s_i^* s_i) approx 1` forces
`tau(s_1 s_1^* + s_2 s_2^*) approx 2` against `tau(1) = 1`: the
TRACE ALONE already sees a defect of `1` here.  This is why the
Leavitt lane, unlike the pure arithmetic lanes, has a trace-visible
seed — the refinement-blindness bites only at the NEXT level, when
the defect is pushed into the group `EL(R)` (a genuine group with
finite-dimensional approximate reps) and the block structure must
track WHERE the ring-level `2 = 1` obstruction is absorbed.  So the
PI-degree observable is needed not for the seed (trace suffices) but
for the transport: to certify that the absorbed defect cannot be
rectangularly refilled as the compressor chain nests.  This locates
the proposal precisely: it is a statement about defect LOCATION under
the nine-leaf corner chain, seeded by a trace-visible `2 != 1`.

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
