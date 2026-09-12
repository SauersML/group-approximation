---
rg: 2
id: fournier-facio-group-hyperlinear
kind: claim
title: The Fournier--Facio torsion-free nonsofic group is hyperlinear
distinct_from:
  fournier-facio-group-matricially-stable: That is operator-norm stability and is already established; it gives no normalized-Hilbert--Schmidt microstates.
  fournier-facio-universal-frobenius-stable-t-embedding: That concerns unnormalized Frobenius stability of a related universal construction; this asks for canonical normalized-HS models of the concrete nonsofic group.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

The finitely presented torsion-free group `G` fixed in
`fournier-facio-torsion-free-skeleton` has canonical normalized-Hilbert--
Schmidt microstates, equivalently its group von Neumann algebra embeds in
`R^omega`.

The established operator-norm and unnormalized-Frobenius stability theorems
do not decide this claim.  Its exact state-form witness is isolated by
`fournier-facio-hyperlinear-iff-singular-near`.

## Attempts

The live attack is
`fournier-facio-hyperlinear-from-singular-near`: build the purely singular
amenable near representation isolated by the exact criterion.  The obvious
stability transfer is unavailable.  Operator-norm asymptotic triviality and
unnormalized Frobenius stability allow no conversion of a normalized-HS
microstate defect, because a defect supported on `o(d)` dimensions is cheap
in normalized HS and remains order one in both of those stronger metrics.

**Necessary structure (2026-09-11).**  `G` contains the wreath product
`S wr Z` of its simple factor by the compression letter `t_1`
(`fournier-facio-group-contains-simple-wreath-shift`), and every nontrivial
quotient of `G` contains it faithfully
(`fournier-facio-nontrivial-quotients-contain-simple-wreath`).  So this
positive branch requires the simple factor `S` to be hyperlinear.  Every
nontrivial tracial model also carries a proper Hilbert-hotel shift on the
`Gamma`-commutant, with relative commutants growing by copies of `L(S)`
(`fournier-facio-regular-models-carry-commutant-shift`).  The survivor audit
in the linked artifact shows that the recorded witness fences use `G` only
through nonsoficity and torsion-freeness.  It also recommends an
infinite-component witness in which `t_1` acts as a bilateral tensor shift,
built on the self-similar tail `Gamma >= J_1 x t_1 Gamma t_1^-1`.

**Positive-side gates (2026-09-11, second pass).**  That construction was
attempted.  It stops at three gates, and none of them is a gap in the tensor
bookkeeping.

1. *Slot geometry.*  Both compressors build the binary-tree lamp group
   `(+)_(w in {1,2}^*) S_w` inside `Gamma`
   (`fournier-facio-compression-tree-lamp-group`).  `S_2` commutes with every
   `J_k`, so a Z-indexed slot model has no room for it, and any model has to
   be indexed by the rooted binary tree.
2. *The simple factor.*  A witness restricts to a hyperlinear model of `S`.
   The graph knows of no hyperlinear finitely presented infinite simple group,
   torsion-free or not (`fp-simple-nonsofic-group` lists every Thompson-like
   group as open; `leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear`
   records the same gate for `V`).  The soft permanence theorems cannot
   supply one.
   - A finitely presented simple group is isolated in the space of marked
     groups: near it lie only its marked quotients in which a fixed
     nontrivial word survives, and by simplicity that is the group itself.
     So a marked limit of hyperlinear groups gives nothing new.
   - A residually amenable infinite simple group is amenable.
   - The one live permanence route is an amalgam or graph of hyperlinear
     groups over infinite amenable edge groups (Brown--Dykema--Jung for
     `R^omega` embeddings over amenable subalgebras).  No finitely presented
     infinite simple torsion-free group with such a splitting is recorded
     here.
3. *The Kazhdan subgroup.*  `Gamma = pi(P)` is an image of the Osin
   small-cancellation Kazhdan group containing a universal finitely presented
   torsion-free group `U`, and Hull's theorem controls the kernel only on
   finite sets.  So the elements of `Gamma` outside
   `pi(S) alpha_1(Gamma) alpha_2(Gamma)` are not given by any explicit
   self-similar formula.  A witness has to model `Gamma` itself, which gates
   through `fournier-facio-compression-subgroup-not-hyperlinear`, now owned by
   a separate lane.  A model would also need unitaries `v_1,v_2` in `R^omega`
   whose conjugations compress `N = u(Gamma)''` onto commuting subalgebras
   with `N >= L(S) tensor Ad(v_1)(N) Ad(v_2)(N)`, compatible with all extra
   relations of `G`.  Here `G` is a proper quotient of the double ascending
   HNN extension of `Gamma`, since `G` is Kazhdan and that extension maps onto
   `F_2`.  The existence of such a self-similar embedding in `R^omega` is
   exactly the open question, not a construction step.

So the positive tensor model is on hold behind gates 2 and 3.

**Two structural facts (2026-09-12).**

- *Rigid defect.*  `Gamma <= G` is a rigid pair whose defect contains
  `pi(S)` (`fournier-facio-group-carries-rigid-defect`).  So this claim implies
  `hyperlinear-group-carries-nontrivial-rigid-defect`
  (`hyperlinear-rigid-defect-from-fournier-facio`).  It refutes the hyperlinear
  defect criterion for every rigid configuration at once, and is at least as
  strong as a counterexample to `kt-centralizer-normalization-hs`.
- *No universality.*  `P` contains a universal finitely presented torsion-free
  group `U`.  If `pi` were injective on `U`, `G` would contain every
  recursively presented torsion-free group, and this claim would be equivalent
  to their joint hyperlinearity.  The construction does not give this.
  Hull's Theorem 7.1(b) makes `pi` injective only on a finite ball, and
  injectivity on `S` comes from simplicity, which `U` lacks.
