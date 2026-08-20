---
rg: 2
id: relative-rank-one-fanizza-groupification
kind: claim
title: Groupify the Fanizza computation through the fixed-pivot relative Pauli bit with constant HS loss
artifacts:
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
  - experiments/minimal_rank_one_support_compiler.py
distinct_from:
  multiplicity-return-transducer: that asks for an arbitrary fixed-BCS recurrent multiplicity return at fixed packet scale; this fixes the local packet to the 128-element support compiler and the quantitative computation to the Fanizza L-family.
  constant-hs-sound-self-detecting-tape-groupification: that asks for a dimension-sensing multiplicity tape and a runtime-independent terminal flag; this uses an existing Turing BCS recurrence and transports only one fixed two-dimensional relative packet.
  zpc-context-mismatch-transducer: that lowers readable predication contexts to an LCS while charging context disagreement; this asks directly for a finitely presented group and uses a relative Pauli multiplicity coordinate rather than selector support.
---

Construct a computable map from a Turing machine `M` to a finite group
presentation `Gamma_M=<S_M|R_M>` and a word `w_M` satisfying the nonhalting
word-survival clause of `hs-pcp-boone-compiler`, together with the following
dimension-free soundness interface.

1. Each nonlinear support-containment primitive in the Fanizza BCS is replaced
   by the fixed packet `A_sub<=B_sub` of
   `support-failure-packet-has-explicit-hs-payment`.  Selector phases are
   context-local; they are not identified as globally central group elements.
2. Every sufficiently accurate normalized-HS microstate exactifies these fixed
   packets with `o(1)` loss and exposes, on violation mass `q`, three rank-one
   endpoint-sharing transport laws satisfying `(RNS1)`.
3. The three transport failures are evaluations of fixed group relators.  The
   rank-one floor and the explicit packet payment combine to give

```text
E_local >= c q - o(1)                                  (RRG1)
```

   for one universal `c>0`, independent of matrix dimension, computation
   level and runtime.
4. The polynomial Fanizza relation decompositions feed these local estimates
   through their exponentially weighted recurrence without changing `c` into
   a runtime-dependent constant.
5. The marked completeness channel is separate from the collapsing projection
   `D`: `w_M!=1` on the nonhalting side, and separation of `w_M` creates the
   initial positive relative-Pauli carrier to which `(RRG1)` applies.

Then there are machine-independent constants `delta>0` and
`alpha<sqrt(2)` such that the halting-side microstate collapse required by
`hs-pcp-boone-compiler` holds.

**Mandatory falsification tests.**  The construction must fail when its BCS
input is replaced by a classically unsatisfiable CSP; otherwise it has merely
globally centralized the selectors and contradicts the hyperlinearity of a
finite graph of finite groups.  It must also explicitly use clause 5; taking
the Fanizza projection `D` itself as the nonhalting mark contradicts
`fanizza-nonmember-signal-is-not-a-separated-mark`.

## Attempts

- **Direct amalgamation over `z_e,z_f` dies.**  The selectors are central in
  every support packet.  Identifying them between contexts makes them central
  in the generated group, turns the contextual BCS into a globally commuting
  CSP, and passes the mandatory classical falsification test for the wrong
  reason.
- **Using `D` as the initial carrier dies.**  On the nonmember side the cited
  estimate gives `phi(D)=0` in every perfect strategy.  It cannot also witness
  marked separation; the Boone/self-reference word must enter through a
  distinct coupling relation.
- **Current live attack.**  Apply
  `non-ce-bcs-has-robust-approximate-energy-gap` to the original shared words
  before packet correction, exactify each fixed 128-element packet locally,
  and use a stable-letter triangle of *relative commutator pairs* rather than
  identifying selector centers.  The unproved step is that the three locally
  corrected relative `M_2` factors have the shared endpoint marginals `(RNS1)`
  with total correction cost controlled by the original fixed-word energy.
