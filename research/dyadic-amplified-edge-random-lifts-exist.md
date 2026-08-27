---
rg: 2
id: dyadic-amplified-edge-random-lifts-exist
kind: claim
title: Construct amplified common-edge permutation lifts with Bass--Serre normal-form separation
artifacts:
  - research/artifacts/dyadic-iwahori-random-lift-audit-2026-08-21.md
distinct_from:
  unamplified-iwahori-sheets-have-two-thirds-defect: that refutes the raw three-sheet block; this asks for amplified finite vertex actions whose internal cycles absorb that defect and whose alternating orbit geometry remains tree-like.
  iwahori-local-global-defect-question: that asks to correct unitary almost-representations in normalized Hilbert--Schmidt norm; this is a finite permutation construction designed to prove soficity of one set action.
---

Put `A=C_0 *_B C_1 = PSL_2(Z[1/2])`, with the two edge embeddings written
as in `iwahori-question-as-square-root-of-parabolic`.  Prove that for every
finite normal-form window `W subset A`, finite coset window `E subset A/C_0`,
and `epsilon>0`, there are a finite set `Omega` and **exact** finite actions
`rho_j:C_j->Sym(Omega)` such that:

1. the two images of each generator `T,w` of `B` disagree on fewer than
   `epsilon |Omega|` points;
2. if `rho(g)` is evaluated using fixed amalgam normal forms, then on at
   least `(1-epsilon)|Omega|` basepoints the blocks

   ```text
   Orb_(rho_0(C_0))(rho(r_x)^(-1) omega),   x in E,
   ```

   are pairwise distinct.

Here `W` is required to contain the chosen representatives, the tested
products, and the finitely many normal-form reductions used by the orbit
window.  No separate approximate action is hidden in the criterion:
`rho_0` and `rho_1` live on the **same** `Omega`, and evaluating words in
these two actions is the common finite approximate `A`-action.

The exact vertex actions are important: since `C_2*C_3` has no relation
between its torsion generators, arbitrary approximate vertex actions can be
corrected generator by generator.  The unresolved content is the **common
edge coupling plus normal-form separation**.  Raw degree-three sheets fail
by `unamplified-iwahori-sheets-have-two-thirds-defect`; an amplification must
use internal parabolic cycles and a coupling not trapped by that finite
permutation character.  Hamming agreement of the two edge generators makes
every fixed normal-form reduction valid off `O_W(epsilon)|Omega|` points by
a union bound.

The single parabolic equation is not itself the remaining obstruction:
`doubled-odd-amplification-erases-iwahori-parabolic-defect` constructs exact
square roots after a two-copy odd-cycle amplification.  The hole is the
simultaneous extension of such a root to the second `C_2*C_3` vertex, the
second edge generator, and the normal-form separation condition.

## Exact dessin coordinates and two eliminated random models

Write one modular action as a permutation pair `(A,Y)` with
`A^2=Y^3=1`.  In the edge coordinates of
`iwahori-commensurator-nielsen-involution`, its restriction is

```text
U=AY,                 E=AY^2AYA,
alpha(U)=U^(-1)E,     alpha(E)=U^(-1)EU.              (DAE1)
```

Thus the surviving finite problem is completely explicit: construct two
exact torsion pairs `(A_0,Y_0),(A_1,Y_1)` and a point relabelling for which
the two pairs in `(DAE1)` are Hamming-close, while the incidence graph of
the two modular orbit partitions has the required finite injectivity
radius.

Two natural probability spaces are now rigorously excluded.
`dyadic-radial-shell-couplings-have-one-third-boundary` proves that arbitrary
finite mixtures of genuine tree spheres have weighted boundary at least
`1/3`; exponential shell growth defeats radial plateaux.
`random-iwahori-actions-resist-nielsen-matching` proves that two independent
uniform edge actions `(U,E)` stay at constant Hamming distance after every
point relabelling with overwhelming probability.  Therefore neither random
tree shells nor independently sampled high-girth edge Schreier graphs can
work.  Any positive construction has to sample **inside a correlated
coupling of the two modular extension loci** and randomize only the
remaining orbit incidence.  Counting or constructing that conditioned
locus is the smallest explicit unresolved lemma.
