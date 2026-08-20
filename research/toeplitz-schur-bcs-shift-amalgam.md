---
rg: 2
id: toeplitz-schur-bcs-shift-amalgam
kind: claim
title: One finite amalgam synchronizes the Fanizza shift with every Toeplitz Schur tape cell
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

OPEN. Construct a finitely presented group `Gamma_*` with the following
simultaneous syntax and completeness properties.

1. It contains the Toeplitz--Steinberg base and a stable letter `t`
   implementing the injective coefficient endomorphism `sigma`.
2. It keeps the Fanizza shift `U=U_1U_2` distinct from `t` and imposes the
   finite diagonal-covariance relations of
   `diagonal-covariance-synchronizes-hnn-and-bcs-shifts` on the finite base
   word menu. Thus conjugation by `t^n` transports every input control exactly
   as conjugation by `U^n`, without killing the HNN height character.
3. For the finite menu of base BCS propagation predicates, finitely many
   Schur packet generators lie in one bounded Toeplitz head. Their *input*
   central selector words are identified with the corresponding base BCS
   involution words. Conjugating the finite input relations and the repeating
   module-return incidence by `t^n` gives every level-`n` packet relation used
   in `(SDL2)`; no nonlinear output is named as a scalar word.
4. All derived level-`n` packet, expander, and overlap relations have
   polynomial derivation cost. In particular, every term in the fixed
   decomposition of `(FDB1)` is wired to a packet return incidence so that an
   inactive selector sector contributes to the adjacent weighted
   multiplicity-vector discrepancy.
5. There is an exact unitary representation in which the marked involution
   word `w` corresponding to `x_D` is nonidentity.

The packet predicates are oriented to equal one on propagation-satisfying
assignments. Exact context-local packet extensions preserving the marked BCS
word are supplied by
`context-local-schur-packet-marked-extension`; they do not
require supported sectors to have equal finite dimension, because infinite
multiplicity absorbs every fixed packet size. Clause 5 must nevertheless be
proved for the **joint** amalgam: those local extensions cannot simply be
declared compatible with the whole Toeplitz--Steinberg return representation.

Literal identification `t=U` is impossible: `U` is a product of two
involutions and is therefore conjugate to its inverse, whereas the strict HNN
shift has height one. This is the obstruction in
`ascending-hnn-shift-cannot-be-an-involution-product`. Diagonal covariance is
the height-preserving replacement and also supplies a tensor-product exact
marked model for the uncoupled synchronization skeleton.
Its shifted input-word cost is already controlled by
`diagonal-covariance-has-quadratic-hs-word-cost`, so the synchronization part
of clause 4 is no longer open. The remaining content of clauses 3--4 is the
module-return incidence and its payment, not propagation of the two clocks.

The phrase "selector/packet relation" in clause 3 must not identify a
derived nonlinear projection such as `P_tilde_n` with a scalar selector word.
That is impossible by `schur-rank-output-is-not-a-scalar-selector`. The
amalgam must instead connect the output `A`-module multiplicity of one rank
gate directly to the input `B`-module multiplicity of the next gate—the
Morita/restriction incidence used in
`oriented-schur-restriction-mass-identity`.
Nor can that incidence be a plain stable-letter conjugacy of finite packet
subgroups: `hnn-conjugacy-cannot-return-schur-morita-multiplicity` shows that
unitary conjugacy preserves the very multiplicity which the rank gate must
double. The word "amalgam" here therefore requires a Toeplitz corner,
projective-cocycle, or adjoint-channel mechanism beyond a graph of finite
groups.

## Attempts

- Add one unrelated packet at every tape level: syntactically infinite and
  therefore unusable. Diagonal covariance reduces all shifted input controls
  to finitely many base relations.
- Identify `t=U`: invalid, because it destroys the ascending-HNN height
  character. Keep both shifts and centralize their difference on the finite
  input menu.
- Tensor independent BCS and Toeplitz representations: this does not satisfy
  the selector identifications.
- Active exact-model construction: extend the nonzero BCS representation by
  its contextwise satisfying Schur spin packets, add countably infinite
  universal multiplicity for every finite base packet type, and use induced
  representations of the finite amalgam so the Toeplitz--Steinberg and BCS
  restrictions agree. The desired BCS summand must remain reducing so its
  nonzero `D` carrier is not lost. The unresolved check is simultaneous
  compatibility of all base context packets with the single stable-letter
  action.
- Scalarize each derived projection and conjugate the base relation: invalid.
  The derived intersections are nonlinear Boolean functions of commuting
  selectors, and the Schur gate exposes them only as module multiplicity.
  The active construction must present a finite repeating **bimodule edge**,
  not a new central reflection word.
- Conjugate the output finite packet subgroup onto the next input packet:
  invalid. A stable letter gives unitary equivalence of the two restrictions,
  so their type multiplicities agree instead of acquiring the factor two.
