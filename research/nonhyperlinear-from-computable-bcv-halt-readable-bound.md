---
rg: 2
id: nonhyperlinear-from-computable-bcv-halt-readable-bound
kind: route
title: Diagonalize a uniform BCV readable bound and embed the resulting quotient in the universal host
target: non-hyperlinear-group
requires:
  - bcv-halt-completeness-has-computable-readable-factor-bound
  - computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap
  - finite-readable-translate-algebra-groupifies-zpc-gap
  - mikaelian-explicit-higman-embedding
  - local-approximation-properties-are-marked-closed
---

Apply the computable BCV bound from the first prerequisite to the bounded
diagonal theorem.  It supplies a finite tailored game `G_(M_0)` on a
nonhalting instance with a perfect ZPC-IRS strategy, a strict quantum gap,
and a full readable translate algebra with finitely many atoms.

The finite-readable groupification theorem applies to any atom orbit and
constructs a finitely presented nonhyperlinear stabilizer quotient `K_T`.
This already proves existence of a nonhyperlinear discrete group.

For the fixed explicit endpoint used elsewhere in this graph, take the
computable free product of the enumeration of all finite group presentations
and apply the Mikaelian--Higman embedding once to obtain the fixed finitely
presented universal host `V`.  The group `K_T` embeds in `V`.
Hyperlinearity passes to subgroups by the local-approximation prerequisite.
Thus `V` cannot be hyperlinear.
