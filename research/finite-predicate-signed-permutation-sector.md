---
rg: 2
id: finite-predicate-signed-permutation-sector
kind: claim
title: Every finite Boolean predicate is the joint spectrum of an irreducible finite-group sector
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  predicate-rank-gate-doubles-restriction-multiplicity: that stores a predicate in a factor-two restriction multiplicity of nested class-two groups; this stores the allowed assignments directly as the joint spectrum of commuting involutions in one irreducible signed-permutation sector.
  finite-selector-gadget-induction-barrier: that says compatible selector characters cannot simply be deleted from every finite-dimensional representation; this builds one selected finite irreducible sector whose spectral support is a prescribed finite set.
---

For every nonempty finite set `S subseteq {+1,-1}^k`, there is a finite group
`H_S`, an irreducible complex representation `pi_S` of dimension `|S|`, and
commuting involutions `X_1,...,X_k in H_S` whose joint spectrum in `pi_S` is
exactly `S`, each point occurring with multiplicity one.

Explicitly, on the basis `(e_s)_(s in S)` take all diagonal sign matrices,
adjoin one cycle acting transitively on the basis, and let `H_S` be the finite
signed-permutation group they generate.  Define `X_i e_s=s_i e_s`.  This gives
an honest finite-group CPU sector for an arbitrary nonlinear local predicate.

The claim is local.  It does not say that approximate group representations
select this irreducible sector with positive density, or that sectors for
different local predicates synchronize.  Those are global carrier and
holonomy problems in
`constant-hs-sound-self-detecting-tape-groupification`.

