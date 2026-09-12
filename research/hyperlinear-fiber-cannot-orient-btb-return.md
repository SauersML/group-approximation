---
rg: 2
id: hyperlinear-fiber-cannot-orient-btb-return
kind: claim
title: A fiberwise hyperlinear cross-edge system cannot orient an unpinned BTB carrier
distinct_from:
  btb-three-line-tree-retains-multiplicity-return-gauge: That treats independent edgewise swaps and recursively chooses their gauges; this permits arbitrary finite cross-edge words and identifies their induced active-fiber presentation as the exact obstruction.
  kazhdan-and-transverse-packets-cannot-orient-clifford-twist: That uses one Clifford implementer and a spectator sign; this treats the whole protected BTB--E5 Schur fiber and any finite graph of actor and edge letters.
  one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum: That closes the last gauge of one holonomy cell; this gives the amplification countermodel whenever the complete typed multiplicity presentation has asymptotically exact matrix models.
---

**ESTABLISHED LOCAL-CARRIER NO-GO.**  Exactify the fixed protected
BTB--E5 packet and restrict to one finite list of authenticated outer types.
Every packet-reducing carrier and every typed source have Schur form

```text
Q=direct_sum_lambda 1_(V_lambda) tensor q_lambda,
F=direct_sum_lambda f_lambda tensor q_lambda.          (FHC1)
```

Now adjoin any finite collection of actor letters, edge intertwiners, and
cross-edge relators.  Substitute the authenticated finite-dimensional outer
matrices in those relators.  The equations left on the anonymous
multiplicity factors form the **active multiplicity presentation**
`M_act`.  This includes relations containing several adaptive edge letters,
property-`(T)` covariance tables, torsion clauses, and stable finite-subgroup
tables.

Suppose `M_act` has finite-dimensional normalized-HS models with defect
tending to zero on every active outer type used by `F`.  Then these rows
cannot imply a positive overlap loss uniformly for **all** packet-reducing
carriers.  They also cannot imply it for a prescribed carrier whose reached
multiplicity projections split the active model block-diagonally.

Indeed, let `theta_n` be such a model and amplify it by an independent
two-dimensional spectator:

```text
theta_n'(g)=theta_n(g) tensor I_2,
q=I tensor [[1,0],[0,0]].                              (FHC2)
```

All defining defects and all normalized word moments are unchanged.  Every
actor and every cross-edge word preserves `q`.  Tensor the stationary outer
packet model with `(FHC2)` and choose the packet-reducing multiplicity carrier
to be this invariant half.  For every proposed return `W`,

```text
W F W^* <= Q,
tau(Q W F W^* Q)=tau(F),                              (FHC3)
```

while the complete packet, actor, covariance, torsion, and cross-edge
defect tends to zero.  Spectator amplification also preserves whatever
finite canonical word-moment window the unamplified model realizes.

There is an essential qualification.  In the canonical finite-tree route the
initial carrier is the fixed group-algebra projection `e_0`.  Under spectator
amplification it becomes `e_0 tensor I_2`, not `e_0 tensor q`; subsequent
carriers are the prescribed minimal reducing hulls and likewise amplify with
the full spectator identity.  The half in `(FHC2)` is therefore not, merely by
being reducing, a carrier reached by that recursion.  Hence this theorem does
**not** refute path-specific `(CBR3)`.  It applies to that path only after one
proves that the active solution can be installed block-diagonally on the
actual reached projections.

Consequently neither property `(T)` nor normalized-HS stability changes the
conclusion.  A Kazhdan estimate can move an approximate intertwiner close to
the exact intertwiner space, but `(FHC2)` lies exactly in that space.  Finite
group exactification has the same kernel.  If the actor is irreducible
before amplification, its amplified commutant still contains `M_2`, and
the projection `q` has zero adjoint-expander energy.

This gives the precise boundary for universal-carrier arguments using mixed
cross-edge words.  Such an argument needs the outer-type specialization to
have a
dimension-independent active-fiber floor

```text
inf_(m,theta:M_act->U(m)) E_act(theta) > 0.             (FHC4)
```

Absence of an exact finite-dimensional solution is insufficient; a sequence
of approximate solutions still gives `(FHC2)--(FHC3)`.  If the specialized
rows are an ordinary untyped group presentation, the trivial representation
already makes `(FHC4)` impossible.  Fixed projective outer phases can remove
that trivial solution, but unless the resulting typed presentation has the
uniform floor `(FHC4)`, spectator amplification again aligns the carrier.

Thus a universal-carrier cross-edge row must be payload-conditioned in a
stronger sense than sharing an edge letter: the forbidden BTB fiber must
activate a typed multiplicity presentation with an HS floor, while that fiber
is absent in the perfect tracial model.  The path-specific alternative remains
open: the fixed seed and minimal-hull recursion might forbid the block
diagonal spectator placement even though arbitrary reducing subprojections do
not.  Importing a Kazhdan or stable actor whose active presentation already
has `(FHC4)` merely imports the missing nonhyperlinearity engine; property
`(T)`, relative spectral gap, and finite subgroup stability alone do not
manufacture it.

DERIVATION
fiberwise-hyperlinear-cross-edge-no-go-proof
