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
  finite-multipath-average-coercivity-has-exact-julia-absorber: that proves finite additive paths coerce their pairwise Gram energy only after complementary leakage is controlled; this must construct that carrier control from native Kac--Moody relations.
  triangle-kernel-relators-charge-authenticated-corner-leakage: that proves the native kernel words pay all complementary leakage on a positive carrier; this must still identify one compressed word with the desired finite-label multipath block.
  km-triangle-local-bimodules-have-finite-nonflat-models: that gives exact regular charts and pairwise overlap intertwiners with a nontrivial native kernel cycle; this must use the kernel relator itself to close the common carrier.
  reynolds-defect-cut-gives-regular-relator-corner: that constructs a large regular-overlap carrier and polar two-path corner for one kernel word; the summed-Reynolds claim below supplies its finite-family upgrade.
  summed-reynolds-cut-synchronizes-kernel-corners: that gives one overlap-subgroup regular carrier and mutually close polar corrections for the whole kernel basis; this must transport that carrier through the rank-two vertex charts.
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

## Additive multipath interface

Allowing a coherent same-block sum does leave the projective-groupoid
absorber, but addition alone is still insufficient.  The established identity
`finite-multipath-average-coercivity-has-exact-julia-absorber` applies to any
finite family of equal-source/equal-range corner unitaries, even when the
paths entangle label and multiplicity coordinates.  Their average loses
corner-isometry mass by exactly

```text
1/(2m^2) sum_(i,j)||A_i-A_j||_2^2.
```

If a native global unitary has this average as a nearly invariant corner,
that identity is the desired finite coercivity lemma and forces path
consensus with constants `2m^2` and `4m^2`.  Without invariance, the Julia
dilation puts the average in the corner of an exact finite-dimensional
unitary and sends precisely the same Gram energy into the complement.

The first surviving construction target is therefore exact: identify one
Curtis--Tits multipath block on a positive regular carrier and prove either
small complementary leakage or an independent relator-energy charge for that
leakage.  More paths and non-Schur coordinate entanglement do not remove this
carrier obligation.

## Native triangle relators do pay leakage

The triangle presentation has a precise tree-first form:
`G_0=P_12*_(P_2)P_23` is virtually free, and the remaining two-cells are a
free basis `n_a=1` of
`N=ker(P_1*_(P_0)P_3 ->> P_13)`.  These relations are analytically sufficient
once the correct corner is named.  By
`triangle-kernel-relators-charge-authenticated-corner-leakage`, for every
projection `q` of trace `beta`,

```text
tau_q(q pi(n_a)^*(1-q)pi(n_a)q)
 <=beta^(-1)||pi(n_a)-I||_2^2.
```

Combining this with the multipath Gram identity gives `(TKL3)`, with exact
constants `2m^2/beta` and `4m^2`.  Hence a correctly compiled kernel-word
compression has no Julia escape.  The narrowed native problem is algebraic:
construct one common regular-core projection of uniform density and expand
`q pi(n_a)q` as, or approximate it by, the desired coherent finite-label
paths.  A further abstract leakage or face-gap lemma would duplicate the
established estimate.

## Local regular bimodules do not compile the common corner

The remaining coefficient step cannot be derived from the local finite
subgroup tables and pairwise overlap maps alone.
`km-triangle-local-bimodules-have-finite-nonflat-models`
uses residual finiteness of the virtually free tree side `G_0` to separate
any chosen `1!=n_a in N` in a finite quotient.  Its quotient-regular
representation is a regular multiple on `P_12` and `P_23`.  After a fixed
common amplification, an independent regular `P_13` chart has exactly the
same restriction multiplicities on `P_1` and `P_3`, so both overlap
intertwiners and all finite group-algebra matrix units match exactly.  The
returned `n_a` holonomy nevertheless remains nontrivial on the tree side and
is identity on the `P_13` side.

Therefore the desired positive carrier and multipath identity must consume
the native relation `n_a=1` during their construction; they cannot be
selected first from local regular cores and then closed formally.  This does
not weaken `(TKL3)`: once such a relation-dependent common carrier is built,
the kernel defect pays its leakage.  It rules out a local-bimodule-only
compiler and isolates the unresolved step as **relation-dependent common-core
extraction**.

## One relation-dependent carrier is available

There is a positive construction beyond the local counterpacket.
For one kernel word `Y=pi(n_a)` and one fixed finite overlap subgroup `H`,
`reynolds-defect-cut-gives-regular-relator-corner` averages
`(Y-I)^*(Y-I)` over `H` and spectrally cuts the result.  The projection `q`
commutes with `H`; for `d=||Y-I||_2<1`, it satisfies

```text
tr(q)>=1-d,
||qYq-(q+B)/2||_(2,q)<=sqrt(|H|d),
```

where `B` is a genuine unitary in `qM_Dq`.  If the ambient `H` chart is
regular, `q` contains a regular summand of relative dimension at least
`1-|H|d`.  Thus one native relation does produce both a uniformly positive
regular carrier and a coherent two-path corner, with a dimension-free
modulus.

The finite-family issue is now settled by
`summed-reynolds-cut-synchronizes-kernel-corners`: sum the Reynolds defect
Laplacians before taking the spectral cut.  If
`E=sum_a||pi(n_a)-I||_2^2`, one common `H`-invariant projection satisfies

```text
tr(q)>=1-sqrt(E),
||q pi(n_a)q-K_a||_(2,q)<=sqrt(|H|)E^(1/4),
||B_a-B_b||_(2,q)<=4sqrt(|H|)E^(1/4).
```

In a regular `H` chart it retains a regular summand of relative dimension at
least `1-|H|sqrt(E)`.  The remaining carrier problem is no longer
simultaneous kernel-word extraction: it is extending this one
overlap-subgroup-invariant carrier through `P_1`, `P_3`, and the rank-two
vertex charts without losing density or recreating the nonflat counterpacket.
