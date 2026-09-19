---
rg: 2
id: hyperlinearity-cannot-see-the-lamp-module
kind: claim
title: Hyperlinearity of a lamp group cannot see the module structure of its lamp
distinct_from:
  icc-property-t-not-w-star-superrigid: That is the group/von Neumann statement — two ICC Kazhdan groups, not isomorphic, with the same group factor; this is the approximation-theoretic consequence, that no hyperlinearity argument can be keyed to the module structure of an elementary abelian kernel, and it names no property (T).
  thom-central-corner-criterion: That is Thom's positive criterion, reducing hyperlinearity of a central extension to embeddability of every twisted corner; this is a negative statement about which data of a semidirect product a hyperlinearity argument is allowed to use, and it concerns the acting module, not a central subgroup.
artifacts:
  - research/artifacts/connes-rigidity-counterexample-2026-08-19.md
---

ESTABLISHED.

Let `D` be a countable elementary abelian group carrying two `H`-module
structures `theta_1`, `theta_2`, and write `Gamma_i = D rtimes_(theta_i) H`.
If the dual actions `alpha_i` of `H` on the compact dual `hat D` are conjugate
by a Haar-preserving Borel isomorphism, then

```text
Gamma_1 is hyperlinear   <==>   Gamma_2 is hyperlinear,
```

and this happens for module structures that are **not** isomorphic — indeed for
pairs whose groups are not isomorphic at all.  So the `H`-module structure of a
lamp kernel is not an invariant of `L(Gamma)`, and no hyperlinearity argument
may be keyed to it without first showing that the particular feature it uses is
visible to the algebra.

## What the transfer does and does not carry

Carried: hyperlinearity, equivalently Connes embeddability of `L(Gamma)`, and
every other invariant of the group von Neumann algebra.

**Not carried: soficity, and not carried: MF-ness.**  A von Neumann
isomorphism says nothing about `C*_r(Gamma)`, so the MF layer of this
repository is untouched by it; and soficity is not known to be a W\*-invariant.
The pair therefore also separates the three approximation notions by
*invariance strength*: hyperlinearity is the one that lives entirely on the
algebra side, which is precisely why a non-hyperlinearity witness has to be a
W\*-invariant while a nonsoficity or non-MF witness does not.

## Where this bears in the corpus

The graph's candidates are lamp groups of exactly this shape.  Kun--Thom's
`W = (directSum_(G/Gamma) Z/2) rtimes G` has
`L(W) = L^infty(prod_(G/Gamma) Z/2) rtimes G`, recorded at
`sofic-radical-hyperlinear-survivor`, and `invariant-graph-clifford-phase`
classifies the central lamp quotients by the `G`-invariant graph carried on
`directSum_X F_2`.  Nothing above disturbs that classification, which is a
statement about groups.  What it forbids is the step after it: reading a
difference in lamp data as a difference in hyperlinearity.  Two lamps whose
dual actions are conjugate give the same algebra even when the lamps are not
isomorphic as modules, and the conjugating map need not be a group
automorphism of the dual — in the witness it is a quadratic shear.

This sharpens, rather than contradicts, the trap already recorded at
`sofic-radical-hyperlinear-survivor`: the gap between an abstract
trace-preserving embedding and a Cartan-preserving one.  Here the Cartan pair
`L^infty(hat D) < L(Gamma)` is itself preserved by the conjugacy, and the
group data is still lost, so even Cartan-preserving information is coarser than
the module.

Recorded as a constraint on proof strategies, not as an obstruction to any
route: no route in the graph currently derives hyperlinearity from lamp module
data, so nothing is invalidated by it.
