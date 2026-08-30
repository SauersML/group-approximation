# STW LXXVII: map-relative O-infinity audit (2026-08-30)

## Problem and definition boundary

Problem LXXVII in the cached v2 text `tmp/pdfs/stw99.txt`, lines 3545--3553,
asks whether a finite-nuclear-dimensional unital homomorphism

```text
phi:A->B
```

from a separable exact algebra is O-infinity-stable when every nonzero
positive element of `phi(A)` is properly infinite in `B`.

For a unital map into a unital algebra the annihilator in Kirchberg's
relative central sequence algebra is zero: an element annihilating `phi(A)`
annihilates `phi(1)=1`.  Thus the relevant algebra is simply

```text
B_omega intersect phi(A)'.
```

This matters: pointwise proper infiniteness gives a decomposition of the
constant unit in `B`, while O-infinity-stability requires decompositions
which asymptotically commute with the entire range.

## Time-sensitive literature audit

1. Schafhauser--Tikuisis--White v2 (addenda through April 2026) still states
   LXXVII as open and stresses that even the identity-map case is the
   pure-versus-strong-pure-infiniteness problem with finite nuclear dimension.
2. Bosa--Gabe--Sims--White, *The nuclear dimension of O-infinity-stable
   C-star algebras*, arXiv:1906.02066,
   <https://arxiv.org/abs/1906.02066>, proves the forward implication used by
   STW: nuclear O-infinity-stable maps with separable exact domain have
   nuclear dimension at most one.  It does not prove the converse in LXXVII.
3. D. Pask, *Nuclear dimension, pure infiniteness and real rank for higher
   rank graph C-star algebras*, arXiv:2607.27691,
   <https://arxiv.org/abs/2607.27691>, proves strong pure infiniteness and
   O-infinity-stability for purely infinite higher-rank graph algebras of
   topological dimension zero.  This is a July 2026 positive identity-map
   class, not the arbitrary map theorem.
4. Exact-phrase and concept searches through 2026-08-30 found no later paper
   claiming the general converse for maps.

This is a targeted primary-source audit, not a proof that no unindexed result
exists.  No literature statement is used as a premise in an established
route below.

## New internal results and frontier

- O-infinity-stability is exactly vanishing of a finite-set centralization
  defect for two orthogonal isometries.  The hypothesis gives only the empty
  finite-set case.
- If `phi(A)` is AF, matrix-unit transport produces the central isometries;
  hence LXXVII is positive for AF-range maps without using finite nuclear
  dimension.
- The hypotheses and conclusion descend to unital quotients of the codomain.
- A precise local colored-centralizer fusion statement is isolated as a
  sufficient frontier.  Its first obstruction is rigorous: proper
  infiniteness of an image element cannot simply be inherited by the
  order-zero supports occurring in a nuclear-dimension approximation.
