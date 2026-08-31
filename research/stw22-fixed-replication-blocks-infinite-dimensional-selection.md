---
rg: 2
id: stw22-fixed-replication-blocks-infinite-dimensional-selection
kind: claim
title: Fixed replication cannot make half-slack matrix fibres infinitely connected
distinct_from:
  stw22-finite-dimensional-factor-bundles-have-uniform-traces: that theorem chooses replication after fixing the finite base dimension and needs only one finite sphere degree; the present obstruction applies when one fixed replication is asked to handle all degrees.
  stw22-matrix-weighted-copy-uniform-finite-degree-fillings: that theorem proves the positive range 2c>=j degree by degree; the present theorem exhibits the first sphere beyond that range and makes it metrically shrink by varying the weight.
  stw99-problem-xxii-tracial-completion-traces-continuous: the root problem remains open over infinite-dimensional or non-countably-generated bundles; this is a no-go for one selection strategy, not a counterexample to trace continuity.
artifacts:
  - research/artifacts/stw22-infinite-dimensional-selection-barrier-audit-2026-08-31.md
---

Fix a finite replication number m>=1.  Among normalized matrix factors,
consider all nonzero weighted-copy fibres

    F_(M_n,m)(a),       m tau(supp(a))<=1/2.             (IB-1)

Every such fibre is homeomorphic to a complex Stiefel manifold
V_k(C^n), where

    k=m rank(supp(a)),       c=n-k.

It is 2c-connected and has

    pi_(2c+1)(V_k(C^n))=Z.                               (IB-2)

Thus no fixed m makes all the values globally C-infinity or contractible.

More sharply, the family in (IB-1) is not uniformly equi-LC^(2m+1).
In M_(2m), take a rank-one projection p and

    a_lambda=lambda p,       0<lambda<=1.

Then m tau(p)=1/2, and a generator of
pi_(2m+1)(F_(M_(2m),m)(a_lambda)) is contained in a Hilbert-sum
2-ball of radius

    2 sqrt(lambda)/sqrt(2m).                             (IB-3)

These essential spheres shrink to one point as lambda decreases to zero
and have no filling even in the whole fibre.

The obstruction persists under strict half slack: using M_(2m+1) and the
same rank-one weights gives shrinking essential spheres in degree
2m+3.  Consequently the direct infinite-dimensional continuation of the
stabilized Michael argument cannot fix one finite m and demand
C-infinity, equi-LC-infinity matrix values.

This does not obstruct the finite-dimensional theorem: for a base of
dimension D it chooses m>=ceil((D-1)/2) and uses only degree D-1.  It
also does not exclude a skeletonwise or telescope construction with
replication increasing, another selection principle, or a different
proof of STW Problem XXII.
