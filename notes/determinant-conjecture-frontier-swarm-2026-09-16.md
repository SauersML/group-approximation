# Determinant conjecture: frontier swarm note (2026-09-16)

Agent: `hi-fron-determinant-conjecture`. Angle: FRONTIER. Target root:
`determinant-conjecture`.

No lock was taken. The work attacks the negative hole
`determinant-conjecture-counterexample-exists` from the shape side: how much
operator-norm room a Serre violation needs.

## 1. Frontier map

The graph as read on 2026-09-16.

**The root and its negation.** `determinant-conjecture` is OPEN, and it is
refuted by `determinant-conjecture-counterexample-exists`, also OPEN. The
reformulation `determinant-conjecture-iff-serre-class-spectra` is ESTABLISHED:
`G` satisfies the conjecture iff every self-adjoint `A in M_n(Z[G])` obeys
every Serre inequality.

**Live positive routes, all resting on OPEN holes.**
- **H1.** `determinant-conjecture-via-integer-root-limits` needs
  `integral-group-ring-spectra-are-integer-root-limits`. By the ESTABLISHED
  `integer-root-limits-are-galois-balanced-serre-measures`, H1 for `G` is
  equivalent to the determinant conjecture for `G` together with Galois balance
  of algebraic atoms. So H1 is at least as hard as the root.
- **H2.** `determinant-conjecture-via-integral-spectral-approximation` needs
  `integral-group-ring-spectra-are-integral-limits`. This implies H1, because
  symmetric integer matrices have real spectrum, and so it is also root-hard.
- **H3.** `determinant-via-unimodular-integral-networks` needs
  `serre-class-from-unimodular-integral-realizability`. This implies the root,
  and through `mdc-via-unimodular-network-serre` also the measured version. It
  is root-hard.

**Dead routes.**
- `determinant-conjecture-via-soficity-of-every-group`: nonsofic groups exist.
- `determinant-conjecture-via-rational-character-models`: Kun--Thom wreath.
- `determinant-conjecture-via-integer-trace-moments`: integer moments do not
  bound log determinants.

**Negative routes.** Routes into the counterexample:
- `determinant-counterexample-from-heavy-eigenvalue`;
- `determinant-counterexample-from-atiyah-counterexample`;
- `determinant-counterexample-via-galois-unequal-atoms`, invalidated by
  `finite-spectrum-integral-elements-obey-determinant`;
- `determinant-counterexample-via-noncomputable-l2-betti-number`.

**Necessary shape of a violation (ESTABLISHED before this lane).**
- Its support generates a nonsofic subgroup
  (`determinant-violation-needs-nonsofic-support-subgroup`).
- Its spectrum is infinite (`finite-spectrum-integral-elements-obey-determinant`).
- Its norm exceeds two (`norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`,
  `integral-operator-norm-below-two-is-quantized`).

**Choice of hole.** Every positive hole is root-hard. The shape side is
tractable, gives checkable propositions, and tells a counterexample search
where not to look. So this lane sharpens the necessary shape.

## 2. State of the art (dated sources)

- **Sofic groups.** Elek--Szabó, Math. Ann. 332 (2005): sofic groups satisfy
  the conjecture. Taken from `determinant-conjecture-holds-for-sofic-groups`;
  not re-read here.
- **Eigenvalues.** Galois balance of eigenvalues over sofic groups: Thom,
  arXiv:math/0701294v3, through
  `integral-eigenvalues-galois-balanced-for-sofic-groups`; not re-read here.
- **Lück's status list.** Lück, arXiv:1901.00827v2, Remark 4.2, as recorded in
  `determinant-conjecture-holds-for-hyperlinear-groups`, read by another lane.
  No class beyond sofic groups, and closure properties, is known to satisfy the
  conjecture.
- **Nonsofic groups.** `openai-leavitt-unit-nonsofic` and the finitely
  presented `explicit-eighteen-relator-nonsofic-group` (graph, ESTABLISHED
  2026-09-12). The sofic proof does not cover every group.
- **Cyclotomic matrices.** McKee--Smyth, arXiv:0705.3599v1 (2007), through
  `cyclotomic-integer-matrices-classified`, read from the PDF by another lane
  on 2026-09-12. Integer symmetric matrices of radius at most `2`.
- **Radius below 2.019.** McKee--Smyth, *Integer symmetric matrices of small
  spectral radius and small Mahler measure*, arXiv:0907.0371 (July 2009). The
  TeX source was read in this lane on 2026-09-16, including Theorem
  `T:spectral radius`, Table 1 and Section 7. The journal version (recalled as
  IMRN 2012) is unverified.
- **Unsigned graphs.** Brouwer--Neumaier and Cvetković--Doob--Gutman classify
  graphs of radius below `sqrt(2 + sqrt 5)`. Cited only as reported in the
  McKee--Smyth introduction; unverified.
- **Mohar's bound.** Mohar (1988) and Lyons--Peres, through
  `fpbs-mohar-adjacency-norm-cheeger-bound`.
- The web-search budget was exhausted earlier in the session, and arXiv
  abstract pages reset the connection. No newer (2024--2026) result on the
  determinant conjecture beyond sofic groups was found in the graph or in the
  sources above. This is not a literature-complete statement.

## 3. What was proven

(to be filled)

## 4. Approaches tried and where each dies

(to be filled)

## 5. Next steps

(to be filled)
