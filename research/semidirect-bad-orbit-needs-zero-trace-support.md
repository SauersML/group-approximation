---
rg: 2
id: semidirect-bad-orbit-needs-zero-trace-support
kind: claim
title: A semidirect bad-character orbit must lie in zero trace support
distinct_from:
  finite-selector-gadget-induction-barrier: That constructs some marked representation containing every compatible selector character; this constrains the restriction of one prescribed tracial state under a normalizer action.
  independent-address-capacity-cannot-drive-selected-atom-growth: That is a mass-capacity inequality for tensor-independent address projections; this is an exact orbit-invariance obstruction for tracial extension to a semidirect product.
---

Let `H` be finite abelian, `L<=Aut(H)`, and `G=H semidirect L`. If a tracial
state on `C^*(G)` restricts to the character distribution `mu` on
`widehat(H)`, then `mu` is `L`-invariant. Consequently, if `mu(chi)=0`, every
character in `L chi` also has zero mass.

Distinct characters in `L chi` do give pairwise orthogonal conjugates of
`e_chi`, so this is the precise obstruction to solving the finite
packing--extension lemma by orbit size alone: the whole desired packing orbit
must already lie in the zero support of the exact contextual trace.
