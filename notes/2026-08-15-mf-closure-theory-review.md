# 2026-08-15 — External review: from marked witnesses to closure theory

Source: user-supplied review session (external model reading the repo),
pasted into the Cairn-ingestion session on 2026-08-15.  This note preserves
the full content and records what became canonical.  Nothing here is
authoritative; the graph nodes are.

## Thesis

`u ->_2 1`, `u^2 = -1`, Clifford signs, finite normal subgroups, and
distinguished witness elements can be removed from the *conceptual* theory
now; at the *analytic* level for arbitrary group-MF obstructions some
replacement mechanism (corner or self-normalized scale) remains necessary —
a genuine operator-norm-versus-rank barrier, not a defect of the present
proofs.  The fundamental object should be `G -> G/Rad_MF(G)` (the MF
reflection) and the fundamental problem "compute the MF closure of the
defining relations".  Compression rigidity becomes a calculus for
generating MF consequences; normal generation and quotient iteration
amplify them.

## Ingestion map (created 2026-08-15)

New claims + routes:

- `mf-relation-closure` (+ proof route from `universal-mf-quotient`,
  `mf-radical-functoriality`) — §"MF radical of relations": `mfroot` is an
  idempotent closure operator; fixed points = normal subgroups with MF
  quotient; non-MF = MF-semantic consequences exceed group-theoretic ones.
- `sound-rule-transfinite-closure` (+ proof route, same prerequisites) —
  transfinite quotient iteration of any sound rule `Delta(H) <= Rad_MF(H)`
  stays in the radical; completeness criterion; obstruction-depth invariant
  in Ideas.
- `noetherian-invariant-compression-rigidity` (+ direct proof) — chain
  condition + equivariance + monotonicity means the invariant cannot see a
  one-sided compression; generalizes `invariant-size-collapse` by dropping
  faithfulness (weaker conclusion, wider scope).
- `zariski-envelope-compression-rigidity` (+ route) — compressed and
  original subgroup have the same Zariski closure in every f.d. rep.
- `invariant-tensor-compression-rigidity` (+ route) — `T(V)^L =
  T(V)^(sLs^{-1})` for every tensor construction; Tannakian enlargement of
  `commutant-no-growth`.
- `kazhdan-tensor-type-transport` (+ proof route) — the review proposed
  this as open; it is in fact a REDUCTION: type-(p,q) fixed tensors are HS
  intertwiners, i.e. off-diagonal asymptotic commutants of the almost
  representation `U^{tensor p} (+) U^{tensor q}`, so the established
  `kazhdan-asymptotic-commutant-transport` (and `scaled-kazhdan-transport`
  for every weight) applies verbatim.  Found during ingestion.
- `matricial-stability-identifies-radicals` (+ direct proof) —
  `Rad_MF = Rad_fd` for matricially stable groups; generalizes
  `map-matricial-stability-non-mf` beyond minimal almost periodicity.
- `semisimple-packet-multiplicity-collapse` (OPEN) — the strongest proposed
  new analytic generalization: exactify locally-finite-dimensional packet
  algebras, measure failure by integer multiplicity defect vectors,
  self-normalize at `‖m‖_1`, apply scaled transport.  Would unify commuting
  lamps, Clifford lamps, Weyl packets, matrix units under "compression
  forces an impossible change of module type".

Edited: `corona-commutant-no-growth` — appended the full consequence
(granting the hinge, the entire compression-centralizer defect lies in
`Rad_MF`, upgrading IntrinsicCompressionMFRadical.lean from 2-norm to
operator norm) and the `mf-invariant-corner-visibility` cross-reference as
the second sufficient meta-principle.

Already in the graph, nothing added: MF reflection universality
(`universal-mf-quotient`), Horn fragments (`mf-universal-horn-obstruction`),
full-radical black holes (`defect-saturation-full-mf-radical`,
`mixed-approximation-black-hole`, TorsionFreeFullMFRadical.lean), the
2-norm no-go (`hs-invisibility-inflation-no-go`), amplification cost
(`corner-renormalization-cost`), corner-visibility dream
(`mf-invariant-corner-visibility`), stable-finiteness/proper-isometry
full-C*-MF obstruction (ProperIsometryFromCompression.lean), matricial
stability lane (`dadarlat-matricial-stability-obstruction` and neighbors).

## Points preserved but not nodified

- **Why some trick is still necessary** (review §15): inflating any
  faithful corona representation by huge identity blocks preserves
  operator-norm separation and kills all normalized-2-norm visibility, so
  universal 2-norm invisibility alone can never contradict MF; the known
  crossings of the metric gap are finite-normal averaging, central spectral
  corners, normal-Kazhdan moving corners, and the self-normalized rank
  scale of torsion collapse.  (= `hs-invisibility-inflation-no-go`.)
- **No universal amplification cure** (§16): any exact continuous unitary
  functor turning a rank-`r` operator-norm outlier trace-visible pays
  `~ sqrt(d/r)` in local Lipschitz constant (FALSE_FERMIONIC_AMPLIFICATION
  Thm 5); so a generic group-MF argument needs a structure-specific
  extraction mechanism unless something much stronger about MF models is
  proved.
- **Full-C*-MF vs group-MF distinction** (§11): for the maximal group
  C*-algebra, one-sided Kazhdan compression alone already manufactures a
  proper isometry (not stably finite) — the no-trick theorem exists; the
  witness machinery is needed only because group MF is weaker (injective
  group map into a corona need not injectivize C*_max).
- **Ten obstruction axes** (§13): semantic closure; compression
  saturation; Noetherian/algebraic-envelope rigidity; invariant-tensor
  rigidity; self-normalized discrete defects; stable-finiteness projection
  obstructions; matricial stability + fd residual; topological/cohomological
  (currently stability-side only; naive PUP index dead); normal/simple
  saturation; universal Horn theory.
- **Corner-visibility second route** (§18): universal invariant-corner
  visibility would convert tracial killing to operator-norm killing, but
  pushes toward MF-implies-hyperlinear strength; the finite-normal and
  normal-Kazhdan corner arguments are the proved special cases.  (Existing
  claim `mf-invariant-corner-visibility`.)
- **External echo**: Kun--Thom 2608.06222 takes the compression
  semigroup/infranormal structure as the central object — consistent with
  the architecture here; the detector, not the compression, is
  target-category-specific.
- Review's suggested next projects: (A) MFClosure packaging, (B)
  CompressionClosure, both now nodes; (C) Tensor/Semisimple compression —
  exact tensor part now a node with route, semisimple part the open claim.
