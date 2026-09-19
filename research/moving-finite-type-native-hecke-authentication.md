---
rg: 2
id: moving-finite-type-native-hecke-authentication
kind: route
title: Select matrix-dependent finite packet types on which the native rows equal the Hecke maps
target: center-chain-common-source-authenticates-native-covariances
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

**INVALIDATED FIXED-PACKET TYPE PROPOSAL.**  Exactify one fixed finite
native packet containing the center-chain projections and, in each matrix
coordinate, choose a collection of its irreducible isotypic carriers.  The
chosen collection may depend arbitrarily on the represented matrix tuple.
Restrict the source and range to those carriers and use the finite packet
type table to identify the two native occurrence rows with the two
common-source Hecke maps.

`fixed-type-and-raw-rank-selectors-do-not-evade-hecke-firewall` invalidates
this proposal.  There are only finitely many subsets of a fixed irreducible
type set.  On a subsequence the source and range type cuts are fixed central
packet projections.  If their discarded Hecke mass tends to zero, canonical
Plancherel convergence and faithfulness force those fixed projections to
contain the entire regular Hecke source and range.  The asserted comparison
then becomes the already impossible fixed regular authentication.

Selecting a proper subspace inside an isotypic multiplicity reservoir is
not a representation-type selection.  It requires an authenticated mixed
block which breaks the reservoir gauge, and remains the surviving case.
