---
rg: 2
id: finite-torsion-free-pattern-realizable-finitely-presented
kind: claim
title: Finite torsion-free patterns are realizable in finitely presented torsion-free groups
distinct_from:
  torsion-free-higman-embedding: that embeds a whole recursively presented torsion-free group into a finitely presented torsion-free one; this realizes only a finite pattern of equations and inequations coming from an arbitrary torsion-free group, which need not be recursively presented at all.
  torsion-free-universal-quotient-recursively-presented: that is the universal torsion-free quotient construction, one of this claim's two inputs; this is the realization statement built from it together with the embedding.
  whitehead-vanishing-finitely-presented-torsion-free: that asserts a Whitehead group vanishes; this asserts a finite pattern of equations and inequations can be realized in some finitely presented torsion-free group, and contains no K-theory. This claim is established and that one is open.
  whitehead-vanishing-recursively-presented-torsion-free: that is a K-theoretic vanishing statement; this is a group-theoretic realization statement used as a tool near it. Notably this claim does *not* imply that one -- transplanting a matrix does not transport the vanishing back.
  torsion-free-finitely-presented-non-mf: that asserts the existence of one finitely presented torsion-free group failing MF; this asserts that every finite torsion-free pattern is realizable in some finitely presented torsion-free group, an approximation-free statement about presentations.
  hnn-torsion-theorem: that is torsion-freeness permanence for HNN extensions, one classical mechanism for building torsion-free groups; this realizes prescribed finite patterns inside finitely presented torsion-free groups and gets its torsion control from Chiodo Theorem 2.2 instead.
  operator-mf-is-a-markov-property: that is about MF being a Markov property of finitely presented groups; this is about realizing finite equation-and-inequation patterns in finitely presented torsion-free groups. No approximation property appears here.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Let `P` be finitely presented, `W` a finite subset of `P \ {1}`, and suppose
some homomorphism `f : P -> G` into a **torsion-free** group has `f(w) != 1`
for every `w` in `W`.  Then there are a finitely presented **torsion-free**
group `H` and a homomorphism `j : P -> H` with `j(w) != 1` for every `w` in
`W`.

**Matrix corollary.**  Let `G` be torsion-free, `A` in `GL_n(ZG)`, and
`B = A^-1`.  Then there are a finitely presented torsion-free `H` and
matrices `Atilde`, `Btilde` in `M_n(ZH)` with the same finite coefficient
pattern as `A`, `B` and with `Atilde Btilde = Btilde Atilde = I_n`.  Take
formal generators for the finitely many group elements occurring in `A` and
`B`, impose exactly the finitely many products that agree in `G`, and put the
finitely many pairwise quotients that are nontrivial in `G` into `W`, so that
the partition of the occurring products into equality classes is the same in
`H` as in `G` and every coefficient collects identically.

## What it is and is not good for

It is the strongest transplantation statement available, and it is enough to
move any *finite* algebraic datum -- an invertible matrix together with its
exact inverse -- out of an arbitrary torsion-free group and into a finitely
presented torsion-free one.  It is genuinely useful beyond Whitehead: it says
finite-support obstructions never need finite presentation of the source
group.

It does **not** transport Whitehead triviality back.  If `Wh(H) = 0` then
`Atilde` factors over `ZH`, but the factorization may use group elements of
`H` far outside the imported pattern, and there is no homomorphism `H -> G`
to carry them home.  See `whitehead-injective-torsion-free-embedding`.  The
direction that does work avoids `H` entirely and stops at the torsion-free
universal quotient, where the comparison map points back at `G`:
`whitehead-vanishing-recursively-presented-torsion-free`.
