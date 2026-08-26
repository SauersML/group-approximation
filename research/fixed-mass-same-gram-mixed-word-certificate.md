---
rg: 2
id: fixed-mass-same-gram-mixed-word-certificate
kind: claim
title: One word-controlled fixed-mass Gram carries every mixed static-game row
artifacts:
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
distinct_from:
  common-partial-isometry-swap-game-compiler: that asks for one literal involutive swap whose off-diagonal block is a common partial isometry; this permits an arbitrary contraction obtained as one block Gram and uses state-local rounding after its mass and covariance are proved.
  one-gram-vector-decodes-a-finite-bcs-strategy: that proves the finite-game Rayleigh inequality for any supplied Gram; this is the remaining ordinary-word construction which must supply that Gram with fixed mass and control all its rows.
  pairwise-cross-grams-do-not-supply-one-game-state: that permits a different state on every edge; this requires one literal block contraction shared by the complete finite verifier.
  source-specific-pointed-rank-router-face: that first replaces the BCS by an independent-set game and uses rank conjugacy on one non-tensor-closed pointed source face; this keeps one global moment selection but no longer asks one Gram word to carry every original BCS row.
---

**OPEN.** Fix either the finite constraint-variable game from
`oracularizable-tracial-nonru-game-exists` or the flat rational refinement
from `lin-pzk-tableau-rational-qc-not-qa-correlation`. Construct a finite
presentation `Gamma`, a marked involution `J`, and a fixed finite packet of
ordinary words with the following properties.

1. The perfect commuting strategy extends to an exact representation of
   `Gamma` with `J!=I`; all Gram rows below vanish there.
2. Every sufficiently accurate canonical-trace matrix model with separated
   `J` decodes one contraction `G` from one fixed block/cross-Gram expression
   and finite PVM rows such that

   ```text
   ||G||_2^2>=m_0 tau((I-J)/2)-o(1)                   (SMG1)
   ```

   for one `m_0>0` independent of matrix dimension.
3. The forbidden and consistency energy of the complete finite verifier,
   evaluated on this same `G`, satisfies

   ```text
   E_G<=K E_rel+o(1),                                 (SMG2)
   ```

   where `E_rel` is the normalized defect of the fixed presentation and
   `K` is dimension-independent.
4. If construction of the rows uses approximate finite-group packets, their
   state-dependent multiplication and left-carrier commutator errors on
   `G` are included in `(SMG2)`. No global normalized-HS exactification or
   near-full carrier alignment is required.

The analytic work after these clauses is established.
`labelled-pvm-branch-gram-gives-lin-corner` makes branch-label
synchronization exact for `G=sum_iF_iT_iE_i` whenever the required labelled
PVMs exist. `two-transport-cross-gram-has-a-fixed-mass-reducing-corner` and
`positive-cross-gram-state-rounds-to-common-pvm` extract a positive common
packet corner from `(SMG1)--(SMG2)`, and
`lin-state-local-gh-is-an-intertwining-exactifier` exactifies the finite
packet without moving its opposite reference action.

The claim is intentionally only the remaining finite-coordinate
certificate. Lin's machinery does not construct `G`, force `(SMG1)`, make a
spectral cut word-visible, or turn the mixed covariance in `(SMG2)` into
ordinary relator energy. In the S3 lane, `(SEC8)` is the conditional
complete-label mass-only form after a joint source PVM has been authenticated;
the hypothesis-minimal endpoint is `(SEC12)`, which requires fixed mass plus
the unanchored endpoint, transitive-role, and return covariance on the same
one-bit Gram. In the Atlas lane,
`(AKC2)` is its same-Gram mixed covariance part. The PZK flat refinement
removes rank denominators but supplies neither clause universally.

## Independent-set bypass

This claim is no longer the unique static-game compiler frontier.
`synchronous-independent-set-reduction-preserves-a-quadratic-gap` replaces
the original Boolean verifier by a fixed game whose complete loss is a sum
of pairwise projection overlaps.  Once the global row PVMs have been
extracted, each overlap can use a pair-local projection source by
`pair-local-independent-set-overlaps-need-no-common-gram`; more strongly,
`rank-conjugacy-detects-projection-overlap` removes a partial-isometry source
entirely.  The initially proposed universal block endpoint
`hybrid-rank-router-authenticates-affine-overlap-blocks` is nevertheless
refuted by tensor closure: local zero-overlap completeness cannot be promoted
functorially to ordinary group representations.  The surviving node is
`source-specific-pointed-rank-router-face`, which conditions routing on one
global non-tensor-closed source face.

That correction neither proves nor refutes `(SMG1)--(SMG2)`.  It does show
that the apparent complete bypass of state selection was too strong.  Lin's
state-local cross-Gram machinery is relevant again as a way to select and
round one pointed moment face, although the new branch need not use one Gram
word for every original verifier row.  This claim remains useful for native
BCS/Atlas constructions whose mixed rows are already expressed on one
word-controlled Gram.

## Fixed-packet localization fence

`fixed-packet-reynolds-cannot-supply-same-gram-certificate` closes the
smallest tempting backend for `(SMG1)`.  Any fixed family of semisimple packet
actions on `V tensor C^N` leaves the full spectator algebra
`I_V tensor M_N`; projections of arbitrary rank, including zero, pass every
fixed Reynolds and packet-incidence test.  Thus packet localization alone
cannot authenticate the fixed positive Gram mass.  Appending functorial
polar/support cuts or a trace-cyclic return does not help, because those
operations exist in the regular finite factor and trigger the established
proper-return firewall.

The target survives exactly in its advertised genuinely mixed form: a word
must act nontrivially on the spectator gauge, or a scalable actor must grow
through the multiplicity coordinate.  A fixed packet calculation followed by
Reynolds averaging is now an exactly fenced approach, not a candidate proof
of `(SMG1)--(SMG2)`.

## Shortest spectator-sensitive word

The first existing ordinary word which genuinely acts on the multiplicity
spectator is the native Whitehead--Hecke anchor

```text
T=Jv,                         T^7=1.
```

By `native-whitehead-hecke-head-has-order-seven-anchor`, attaching a commuting
reservoir involution `D` to either factor changes the seventh power to `D`.
Thus on a reducing carrier the relator gives the exact dimension-free
estimate `||D-1||_2`; unlike every even/projective relative word, this actor
really does see `I_V tensor M_N`.

The shortest compression of that actor is now exactly refuted.
`order-seven-first-exit-supplies-same-gram-mass` tried to use a low spectral
cut of `Q T^*(1-Q)T Q`.  The amplified seven-cycle model has a trace-`1/7`
cut with zero first-exit energy but `ETE=0`, so its compressed seventh power
is maximally wrong.  Accordingly
`order-seven-first-exit-closes-same-gram-certificate` is invalidated.

What survives is strictly stronger and already sharply named: control the
full moving-cut boundary `(1-E)TE`, or all six orbit exits through the seven
stages.  This is the orbit-saturated mechanism of the existing growing
multicut order-seven lane.  The actor is no longer the hole; positive-mass
compression leakage is.

The analytic six-exit step is now closed by
`six-exit-moving-cut-seventh-power-telescope`.  For moving cuts
`E_0,...,E_6`, the seven-factor compressed product differs from
`E_0T^7E_0` by at most the sum of the six intermediate exit norms, hence by
`sqrt(6)` times the square root of their total exit energy.  The remaining
positive-mass extraction is therefore concrete rather than functional-
analytic: find the ungauged full-Gram coefficient bridge of
`el20-six-moving-coefficient-square-bridges`.  The fixed positive signed
Hecke source already supplies the mass; `(ESB1)--(ESB2)` must transport all
of it through the moving charts while the mixed squares lock one reservoir
gauge.  No further telescope inequality is missing.
