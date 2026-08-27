---
rg: 2
id: hecke-quarter-selector-is-untyped-or-rank-preserving
kind: claim
title: A Hecke coset quarter-selector is either unauthenticated or preserved by every finite-edge transport
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs a common positive regular type vector for an arbitrary finite restriction graph; this computes the proposed coset involution cut itself and shows why authenticating that cut turns every Hecke transport into a rank-preserving module isomorphism.
  finite-character-idempotents-have-exact-hnn-transport: that proves matched finite character types can be transported exactly; this proves the complementary obstruction that matched transport cannot change the selector rank, while unmatched quarter-rank data are not transported by the stable letter.
  cyclic-coarse-fine-selector-rows-spread-carrier-error: that supplies the analytic quarter-trace floor after coarse and fine selectors have been decoded; this rules out obtaining that decoding from a finite coset chart and its ordinary finite-edge transports alone.
---

**ESTABLISHED.**  Let a finite group `G` act on `Omega=G/H`, let `s in G`
be an involution, and let `S` be its permutation matrix.  The negative spectral
projection

```text
e_s=(1-S)/2
```

has normalized rank

```text
tr_Omega(e_s)
  = (1/2)(1-|Fix_Omega(s)|/|Omega|).                    (HCQ1)
```

Thus a literal group involution really does give a quarter-rank selector in a
chosen coset module precisely when it fixes half of the cosets.  Its reflection
is the group word `S` itself, so no nonlinear `CZ` syntax is needed at this
stage.

This observation does not authenticate the quarter rank.  In the left regular
module of any finite group containing a nonidentity `s`, left multiplication
by `s` has no fixed points, and hence

```text
tr_reg((1-s)/2)=1/2.                                    (HCQ2)
```

More generally, direct sums of coset modules carry the corresponding convex
combinations of their permutation characters.  Ordinary group relations do
not select the particular summand on which the fixed-coset fraction is `1/2`.
In a finite graph of finite packet groups, the common regular stationary type
therefore makes every nontrivial literal involution a half-selector.  A pair
advertised as coarse `1/2` and fine `1/4` becomes two equal-rank half-selectors
in that exact finite-dimensional model.

Subgroup averages do not repair this.  For

```text
p_H=|H|^(-1) sum_(h in H) h,                            (HCQ3)
```

`p_H` is the projection onto the `H`-fixed space of the represented module,
so its trace is representation-dependent.  In `lambda_G` it is exactly
`1/|H|`.  If an HNN stable letter implements an isomorphism `phi:H->L`, then

```text
t p_H t^(-1)=p_L,       |H|=|L|,                        (HCQ4)
```

and the two projections have equal trace in every tracial representation.
The same statement holds for matched finite-character idempotents and for any
finite orthogonal sum of such matched pieces.

There is consequently a sharp dichotomy.  If one retains an untyped
quasi-regular carrier, `(HCQ1)` can display the desired quarter cut but the
regular stationary representation changes its rank.  If finite packet data
authenticate the carrier and its selector spectrum, then an HNN/Hecke edge
which transports that authenticated data is a unitary module isomorphism and
preserves every spectral multiplicity.  It cannot transport a half-rank cut
to a quarter-rank cut.  Using different authenticated types at the two ends
merely restores the typed-carrier escape: the stable letter does not identify
those types, and a piecewise Hecke unitary can pair only equal-rank pieces.

For completeness, `(HCQ1)` follows because an involutive permutation is a
disjoint union of fixed points and two-cycles.  Each two-cycle contributes one
`-1` eigenvector, giving

```text
rank(e_s)=(|Omega|-|Fix_Omega(s)|)/2.
```

Equations `(HCQ2)--(HCQ4)` then prove both branches of the dichotomy without
an asymptotic argument.

## Consequence for the cyclic coarse--fine endpoint

The cyclic trace lemma remains a valid positive endpoint: if some independent
matrix-only mechanism authenticates carriers `P_i` and literal involutions
whose negative cuts have relative ranks `1/2` and `1/4`, its reflection rows
are already ordinary words and the cyclic sum charges `sum_i tr(P_i)`.
What the coset/Hecke proposal cannot supply is exactly that authentication.
A successful replacement for nonlinear `CZ` syntax must contain a genuinely
non-finite-edge two-cell which selects a quasi-regular multiplicity profile in
finite matrices without turning the coarse-to-fine covariance into a
universal tracial identity.  Finite subgroup averaging, stable-letter
transport, and restriction-graph holonomy alone collapse to `(HCQ2)` or to
rank preservation.
