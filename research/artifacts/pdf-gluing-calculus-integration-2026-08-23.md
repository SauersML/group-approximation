# Gluing-calculus dossier: integration record

**Date:** 2026-08-23
**Scope:** wiring an externally supplied "quotient the local gauge first, then
read the residual obstruction" analysis into the Cairn graph.
**Verdict:** the calculus is correct and useful as a *screening* discipline; as
a *completion* strategy its two headline proposals are ruled out by claims the
repository already held. Two of its structural suggestions survive and are now
nodes. No new route to `non-hyperlinear-group` is created by it.

## 1. What the dossier proposed

Seven experiments, in its own priority order:

1. rebuild `spherical-short-holonomies-admit-local-gauge` as a finite 2-complex,
   take a spanning tree, compute fundamental cycles and integral `H_1`, bound
   filling constants, and finish with the `A_3(F_q)` metric cone;
2. assemble the router rank/moment lattice, generate the locally harmless
   modification directions, compute the cokernel, and search for a primitive
   low-support functional separating the distinguished source from the
   tensor-closure witness;
3. build a packet overlap "conductor complex" and read loop discrepancies as
   relative-commutant holonomies;
4. compute Smith normal forms of the affine-Leavitt depth-`N` rank/multiplicity
   flow matrices, looking for a discrete boundary-escape checksum;
5. linearize the SL3 fold word against a Fox Jacobian, quotient the gauge
   directions, and inspect the residual singular values;
6. prove the projective-tower old-class inclusion primitive modulo the covering
   prime instead of enumerating the saturation coset;
7. materialize the Kac-Moody three-subspace defect as a signed incidence
   complex and take its Smith form.

Plus one hygiene rule (split extensions must pass through coinvariants) and a
terminal reduction claiming that everything now rests on one matrix-only
occurrence-authentication theorem.

## 2. What was already in the graph

Almost all of the dossier's part-2 "terminal reduction" is present, in finer
grain than the dossier states it. Specifically:

- the cyclic checksum `sum_i d_i^2 >= (1/4) sum_i tau(P_i)` is exactly
  `cyclic-coarse-fine-selector-trace-proof` at `a=1/2, b=1/4`, and its
  gauge-independence is the point of that route;
- inequality (2) of the dossier is `(GTC4)` in
  `global-marked-type-cycle-selector-decoder`, together with `(GTC5)`;
- inequality (4) of the dossier is `(ASR1)` in
  `affine-leavitt-source-saturated-reynolds-checksum`, with the exact
  `p^(-2)` versus `p^(-4)` gap and the `(ASR3)` reverse candidate already
  computed and refuted;
- "rank/SNF arithmetic cannot finish" is `finite-rational-rank-flows-are-fd-dense`
  and `atlas-fixed-packet-arithmetic-has-no-hs-gap`;
- "property (T) density control cannot finish" is
  `property-t-hs-positive-density-commutant-no-growth`;
- "fixed words cannot finish" is `canonical-marked-reynolds-return-is-subgroup-intersection`,
  `leavitt-range-sum-fold-does-not-pay-reynolds`, and
  `leavitt-target-return-channel-count-firewall`;
- the SL3 half of the dossier's section 7 is present as
  `five-parahoric-overlap-saturations-give-global-shell-pvm`,
  `kesten-chart-carriers-have-25-over-42-gram-floor`,
  `two-equivariant-shell-pvms-have-independent-coordinate-escape`, and
  `finite-shell-coset-tower-is-a-nonlinear-unstabilized-lift`;
- the split-extension coinvariants rule is already respected: a sweep of
  `research/` for split/semidirect abelianization claims found no node
  asserting `G^ab = K^ab (+) Q^ab`, and `notes/FALSE_INTERMEDIATE_SPLIT_HOMOLOGY.md`
  uses the coinvariant form correctly.

Nothing above was duplicated.

## 3. What the integration ruled out

### 3.1 The cokernel/Smith-form search cannot complete anything

New node: `gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap`.

A checksum `gamma` on `Z^N/im(D)`, for `D` the matrix of locally realizable
repair directions on fixed finite packet rank data, splits into a torsion part
killed by amplification (`APA1` leaves the normalized profile fixed while
landing in `ker gamma`) and a free part whose normalized value is driven to
zero either by profile density (`APA2` plus `RFD2`) or explicitly by
`gamma(m_wit + k m_src) = gamma(m_wit)` at linearly growing dimension.

This disposes of dossier proposals 2 and 4 as completion routes, and of the
Smith-form half of 7. It preserves them as *diagnostics*: `coker(D)=0` or
`m_src = m_wit` in the cokernel refutes a moment vocabulary cheaply.

### 3.2 The metric cone cannot be applied to the spherical gauge system

New node: `spherical-displacement-length-is-not-conjugation-invariant`.

The cloud displacement length `ell_r` is a genuine length — subadditive,
symmetric — but conjugation inflates it from `0` to the full diameter `2`
(swap near pairs, conjugate onto antipodal pairs). The metric cone theorem
requires a conjugation-invariant length as its coefficient hypothesis, so it
cannot be run on `Sym(N)` with this length at all. This failure is prior to,
and independent of, the coboundary-versus-cocycle restriction in
`a3-cone-repairs-to-coboundaries-not-cocycles`.

What survives is sharper than the proposal: `ell_r` *is* invariant to within
`2 rho` under conjugation by a shadow map, which is the only conjugation the
gauge law performs. So a filling argument is available, but only along paths of
bounded length, with the bound fixed by the table.

This disposes of dossier proposal 1 in the form proposed and replaces it with
a well-posed combinatorial question about the fixed table's identities among
relations.

### 3.3 Orbit transport is circular for non-closed tables

New node: `orbit-transport-gauge-needs-a-closed-label-set`.

The most natural constructive attack on the spherical gauge — transport the
regular action along near-orbits — is proved here to work, with corrections of
radius at most `5 rho + zeta` and every tested relation satisfied *exactly* on
the packed region, reducing the entire claim to one near-perfect packing of an
`|G|`-uniform hypergraph. But the construction needs the label set to be
multiplicatively closed, or an almost-invariant subset of it, and demanding the
latter of every finite chunk of a group is the Folner criterion. So the
construction closes the claim exactly for finite-group tables and for amenable
ambient groups, and is circular otherwise.

### 3.4 Local canonicity is not the missing ingredient anywhere

New node: `local-exactification-invariants-cannot-close-gluing-holes`.

Four open endpoints in four lanes share one shape: independent local
exactification determines only a `Gamma_loc`-orbit, and the recorded witness in
each lane was manufactured by exercising exactly that freedom. The residual
gauge group is explicitly known in each case (per-context transport, the
multiplicity involution `V` in `t=R_f tensor V`, tensoring with exact scalar
sectors, the relative commutant `Alg(rho_n(K))'`). Any candidate observable
invariant under the named group is disqualified by inspection, before any
estimate is attempted. Integral cokernel checksums are disqualified twice over.

## 4. What was declined

- **A conductor-complex node (proposal 3).** Its content is already the
  formulation recorded inside `full-packet-bicommutant-synchronization` ("must
  use the cross-root multiplication and compressor synchronization relations")
  and the new invariance node makes the design constraint explicit. A separate
  complex would be a renaming.
- **A terminal "everything reduces to (2) or (4)" node.** The graph's live
  route set into `non-hyperlinear-group` is much wider than the two
  architectures the dossier examined; asserting completeness over it would be a
  false claim of exhaustiveness.
- **The `p=12 l_0-4 l_1-3 l_2` analogy and every other quantitative statement
  imported from the source PDF.** None of it is a fact about this program, and
  the literature-quarantine gate forbids carrying an unverified external
  computation into canonical nodes.
- **Proposals 5, 6, 7 as authored experiments.** They are numerical programs
  for other sessions' lanes (SL3 Fox linearization, projective tower
  primitivity, Kac-Moody incidence). The Smith-form component of 4 and 7 is
  covered by 3.1; the rest is not refuted, merely not this session's lane, and
  no node was written for work not done.

## 5. Net effect on the frontier

No frontier hole was closed and none was opened. Three screening no-gos and one
positive structural theorem were added, one previously route-less frontier hole
(`spherical-short-holonomies-admit-local-gauge`) gained a recorded partial
result and a precise statement of why the cohomological attack is unavailable,
and four lanes gained a one-line disqualification test for candidate
observables.
