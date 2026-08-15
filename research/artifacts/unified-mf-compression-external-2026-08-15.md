# 2026-08-15 — External note: unified MF-compression theory (audit archive)

Source: user-supplied external review session (GPT-assisted, unrefereed),
pasted 2026-08-15, following the closure-theory review earlier the same
day (notes/2026-08-15-mf-closure-theory-review.md).  This file records
the ingestion audit; the canonical content lives in the graph.

## Audit table (this session)

Verified in full before route commitment:

- **Slow-wall counterexample** (their Thm 4.1) -> `corona-commutant-growth-witness`.
  Checked: finite-quotient equalization by cardinality; distortion
  divergence from residual finiteness; both norm estimates; consistency
  with the formalized HS transport (witness is trace-invisible) and with
  `marked-quotients-not-lef` (no conflict: the witness is corona-external
  and the construction needs residual finiteness).
- **Projection collapse bootstrap** (their Thm 6.1) ->
  `corona-projection-collapse`.  Checked: the subgroup
  `E' = <pi(E), 1-2p>` of `U(Q)` is countable; (T) passes to the image;
  witness axioms transfer; and the decisive step — instantiating the
  universal invisibility of `[gamma, w]` at the inclusion `E' -> U(Q)`
  itself — is exactly an application of the kernel-checked
  `actualCoronaMFInvisible_of_involutiveWitness`.
- **Zero-dimensional collapse + component bound** (their 6.2, 13.1) ->
  `zero-dimensional-spectral-collapse`, `spectral-component-motion-bound`.
  Standard functional calculus; quasi-component = component in compact
  Hausdorff.
- **Sign-free factory** (their 14.1) -> `sign-free-compression-amalgam`.
- **Marked-quotient resolutions** -> `commuting-lamp-quotient-not-mf`
  (witness `c_{tau o}`, verified directly against
  `commuting-lamp-quotient-structure`; the manuscript's own wreath
  remark describes the witness), `literal-mark-quotient-not-mf`
  (witness `dbar` in the level-one block; the base `Gbar` preserves that
  block since translations and `SL_3(Z)` preserve the image of `Z^3` in
  `Z[1/2]^3/2Z^3`), `unsquared-defect-mf-invisible` (pullback).

Verified at architecture level (all displayed estimates checked, full
line-by-line bookkeeping not re-derived):

- **`W_Z` is MF** (their Thm 5.1) -> `infinite-cyclic-compression-lamp-mf`;
  with the formalized transport this gives
  `mf-vs-tracial-radical-strict-gap`.
- **Path-MAP lamps** (their Thm 11.2) -> `path-map-lamp-mf`; abelian
  classification (their 5.2) -> `abelian-lamp-mf-classification`.

Recorded OPEN (self-similarity of the iteration not yet verified):

- **`Rad_MF(W/<zeta>) = L_0`** (their §15) ->
  `commuting-lamp-mf-radical-is-level-even`; the lower bound is the
  designated application of `sound-rule-transfinite-closure`.

Not ingested as nodes (already present or deferred):

- Their Thm 2.1 (tracial invisibility + normal (T) => MF invisibility) is
  the manuscript's abstract invisibility theorem
  (`manuscriptAbstractNormalKazhdanObstruction`, formalized); no new node.
- Their §9 (weak-MF => no normal Kazhdan subgroup in the hyperlinear
  residual; Kazhdan-rich weak-MF => hyperlinear): deferred — the
  machinery overlaps the in-flight NormalKazhdanHyperlinearKilled lane
  owned by a peer session; ingest after that lane lands to avoid
  duplicating or colliding with its statements.  The simple-Kazhdan case
  is already formalized (`isHyperlinear_of_simple_kazhdan_weakMF`).
- Their §12 (Zariski envelope / invariant tensors) was already ingested
  earlier today (`zariski-envelope-compression-rigidity`,
  `invariant-tensor-compression-rigidity`).
- Their MF-closure §1/§10-11 were already ingested earlier today
  (`mf-relation-closure`, `sound-rule-transfinite-closure`).

## Correction ledger

- Their §7/“Corollary 14.2” cite the decomposition as
  `E/<w> ~= V *_{B_1} ((Z/2)^8 semidirect B_1)`; the repository's
  established form (`literal-lamp-kernel-clifford-block-amalgam`) is the
  free product of `(Z/2)^8` blocks with `V` permuting blocks — the two
  presentations agree (Bass--Serre), and the route was written against
  the repository's form.
- Their draft Lean file names match the repository API
  (`actualCoronaMFInvisible_of_involutiveWitness`,
  `IsInvolutiveCompressionWitness`) — checked against
  `InvolutionCollapseEndpoint.lean` lines 886-921.

## Addendum: third external note (same day)

A follow-up note reorganized the engine around the Kazhdan projection in
finite C-star targets.  Ingested: the master lemma
(`kazhdan-projection-finite-target-calculus`, with its corner-level second
proof of the normal-Kazhdan obstruction recorded in the card body); the
direct rank-cocycle route to projection collapse
(`corona-projection-collapse-direct-proof`); and the named compression
closure (`compression-closure`).  Its Theorems 2-4 are the repository's
formalized scaled transport and intrinsic tracial invisibility; its
Theorems 7-10 were ingested from the second note; its Theorem 11 is
`sound-rule-transfinite-closure`, formalized this day as `IsSoundIterate`.
Its weighted-inner-product observation — dimension-normalized and
rank-normalized transport are one theorem — is recorded in the master
lemma card.
