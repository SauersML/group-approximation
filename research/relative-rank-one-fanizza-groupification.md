---
rg: 2
id: relative-rank-one-fanizza-groupification
kind: claim
title: Groupify the Fanizza computation through the fixed-pivot relative Pauli bit with constant HS loss
artifacts:
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
  - experiments/minimal_rank_one_support_compiler.py
distinct_from:
  multiplicity-return-transducer: that asks for an arbitrary fixed-BCS recurrent multiplicity return at fixed packet scale; this uses the three fixed packet shapes of the Fanizza L-family, whose largest affine rank matrix has size twelve.
  constant-hs-sound-self-detecting-tape-groupification: that asks for a dimension-sensing multiplicity tape and a runtime-independent terminal flag; this uses an existing Turing BCS recurrence and transports only one fixed two-dimensional relative packet.
  zpc-context-mismatch-transducer: that lowers readable predication contexts to an LCS while charging context disagreement; this asks directly for a finitely presented group and uses a relative Pauli multiplicity coordinate rather than selector support.
---

Construct a computable map from a Turing machine `M` to a finite group
presentation `Gamma_M=<S_M|R_M>` and a word `w_M` satisfying the nonhalting
word-survival clause of `hs-pcp-boone-compiler`, together with the following
dimension-free soundness interface.

1. Each of the three machine-independent nonlinear predicate shapes in
   `fanizza-final-bcs-has-fixed-nonlinear-menu` is replaced by its fixed
   Schur--Clifford packet.  Their affine rank matrices have size at most twelve
   by `fanizza-fixed-nonlinear-menu-has-small-rank-gates`.  Selector phases are
   context-local; they are not identified as globally central group elements.
2. Every sufficiently accurate normalized-HS microstate exactifies these fixed
   packets with `o(1)` loss and exposes, on violation mass `q`, the one extra
   relative Pauli coordinate as three rank-one endpoint-sharing transport laws
   satisfying `(RNS1)`.
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
- **Support-only reduction is insufficient.**  The two-bit packet handles one
  child-without-parent atom but does not encode the fixed six-bit conditional
  partition relation `C18`.  The exact audit is
  `fanizza-final-bcs-has-fixed-nonlinear-menu`; its compact rank gates now
  replace the incorrect support-only premise.
- **Current live attack.**  Apply
  `non-ce-bcs-has-robust-approximate-energy-gap` to the original shared words
  before packet correction, exactify one of the three fixed packet shapes
  locally, and use a stable-letter triangle of *relative commutator pairs*
  rather than identifying selector centers.
  `every-forbidden-atom-has-fixed-schur-pauli-words` supplies literal words
  for each atom's Schur-complement `M_2` factor.
  `fanizza-bad-atoms-have-source-fixed-paired-frames` proves that a
  coordinate-core plus/minus edge can fix the whole source selector center
  and keep the source atom at its rank-two target.  But its coefficient image
  has rank four, whereas the one-sided E5 chart has rank three.  The local gap
  is resolved by
  `fanizza-bad-atoms-have-symmetric-frames`: arbitrary
  weight-two dual baseline words give one common source-fixed rank-three
  kernel for all 26 atoms, after one extra C17 compiler pivot.  That kernel is
  in a different `GL_4(F_2)` orbit, but every escape has `J=+1` and its
  rank-two form is aligned to one common root by a kernel-preserving swap.
  `fanizza-symmetric-kernel-has-two-root-e5-clock` realizes its matching
  one-sided valuation clock by `diag(S,1,I_2)`.  What remains is to couple the
  listed reverse characters into successive valuation layers and control
  the two child copies by the original fixed-word energy.
  `branching-plus-first-hit-exits-forces-hs-floor` shows that no further
  persistence mechanism is needed: the two-child Fanizza balance minus at
  most one exit copy leaves one active copy.  The precise remaining estimate
  is therefore the localized operator version of `(BFE1)` and `(BFE3)` on the
  same exactified packet carrier: `relative-pauli-child-split-gives-one-exit-copy`
  already supplies `(BFE2)` from two literal equal-rank spectral halves, and
  `hard-sign-transport-captures-exit-mass` supplies `(BFE3)` from one central
  intertwining relation plus the corner BCS gap.  The remaining local estimate
  is `(BFE1)` on that common carrier.
  `product-clock-synchronizes-fanizza-and-e5` supplies the finite global word
  placement: `T=UD_L` advances the Fanizza source and E5 boundary together
  while fixing the coefficient packet, and it retains the exact tracial model
  by keeping `U` independent of a trivially represented E5 factor.  Beyond
  `(BFE1)`, the marked initial-carrier interface remains separate.
