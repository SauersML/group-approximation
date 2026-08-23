---
rg: 2
id: compact-hyperbolic-km-regular-microstates-synchronize
kind: claim
title: Regular microstates of one compact-hyperbolic Kac-Moody lattice synchronize globally
distinct_from:
  finite-subgroup-near-regular-has-large-regular-core: that extracts a regular core separately on every finite subgroup; this must align all overlap gauges and kill every Curtis-Tits cycle holonomy.
  three-chart-loop-retains-free-multiplicity-holonomy: that exhibits the abstract free cycle gauge; this asks the native Kac-Moody two-cell relations to control it on the canonical regular branch.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that classifies bare face-flat multiplicity connections and shows curvature repair is presentation stability; this can succeed only through additional native label--multiplicity coupling.
  fixed-finite-label-km-holonomy-is-scalar-or-gapped: that rules out every fixed projective-label Schur-product twist; this still permits growing or genuinely label--multiplicity-entangled overlap maps.
  character-rigidity-equals-hyperfinite-hs-stability: that treats the hyperfinite character branch; this asks for correction of the nonamenable canonical regular branch.
artifacts:
  - research/artifacts/regular-core-holonomy-universal-attack-integration-2026-08-22.md
---

**OPEN.**  Fix an infinite finitely presented simple Kazhdan
Caprace--Remy compact-hyperbolic Kac--Moody lattice `Gamma`.  Every canonical
regular-trace normalized-HS microstate sequence for `Gamma` is, after an
`o(d)` flexible dimension change, `o(1)`-close on a fixed generating set to
a genuine finite-dimensional representation of `Gamma`.

Finite-subgroup exactification already makes every local chart a direct sum
of regular representations up to `o(d)`.  The new content is global: choose
overlap identifications, gauge away a spanning tree, and prove that the
remaining multiplicity-commutant holonomies around the Curtis--Tits/chamber
two-cells are `o(1)`-gauge-equivalent to an exact global representation.
Neither property `(T)`, IRS rigidity, nor local finite-group stability proves
this statement.

## Curtis--Tits face-gap audit

The established classification
`finite-face-flatness-stops-at-fundamental-group-holonomy` rules out a
strictly smaller lemma based only on multiplicity edge gauges and individual
Curtis--Tits face curvature on a common untwisted reservoir.  After a
spanning-tree gauge, the surviving edge unitaries are presentation generators
and the face curvatures are their relator defects.  Repairing them to a flat
connection is therefore the normalized-HS stability problem for the resulting
fundamental-group presentation, while killing the flat connection is its
trivial-representation branch.

For the simple lattice fixed here, exact finite-dimensional global holonomy
is indeed trivial.  That removes exact nontrivial flat countermodels, but it
does not supply a quantitative repair theorem: excluding asymptotically flat
nontrivial matrix holonomy is exactly the regular-branch synchronization
asserted above.  Local spherical residues or isolated Curtis--Tits triangles
can gauge contractible data only.  A genuine decomposition must add a named
relation which couples a regular finite-subgroup label block to its
multiplicity unitary; another bare cocycle or face-gap estimate would merely
rename this terminal target.

## Fixed finite-label twists are exhausted

The first apparent native coupling is to let each overlap transporter have
Schur form `C_s tensor Q_s`, where `C_s` belongs to a fixed finite projective
intertwiner groupoid and `Q_s` acts on the growing regular multiplicity.
`fixed-finite-label-km-holonomy-is-scalar-or-gapped` gives an exact dichotomy.
If one finite label relator is nonscalar, its spectral spread gives a fixed
normalized-HS defect which no `Q_s` can cancel.  If every label relator is
scalar, the `C_s` define a finite-dimensional projective representation of
the simple lattice, hence are themselves projectively scalar and carry no
sector or adjoint-label information.

Thus finite projective cocycles, sector permutations, and monomial finite
bimodule paths do not provide the missing smaller lemma.  The narrow surviving
native target is a **non-Schur overlap coefficient**: a same-block coherent
sum of at least two finite label paths, or an intertwiner which genuinely
entangles label and multiplicity coordinates.  Its construction must be
forced by a named Curtis--Tits relation; merely allowing its finite label
alphabet to grow with the microstate would abandon fixed-scale extraction.
