---
rg: 2
id: schur-flip-wreath-compressor-has-infinite-cocycle-rank
kind: claim
title: One strict wreath compressor gains infinitely many independent Schur flip cocycles
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
distinct_from:
  compressor-fixed-site-growth-infinite: that counts the new fixed sites for the Kun--Thom coset action; this places one explicit Schur flip-square packet at each site and computes the resulting projective cocycle rank.
  clifford-compressor-site-growth: that obtains infinite Pimsner--Popa index from Majorana modes in a Clifford crossed product; this obtains unbounded binary holonomy rank from finite Schur packet factors in a permutational wreath model.
  compressor-amplifies-schur-flip-cocycle-rank: that needs a uniform finite-microstate consequence and finite presentation; this proves the exact tracial model already contains arbitrary rank after one compressor step, with no recursion-depth issue.
---

Fix a Schur predicate packet and let `H_f` be the finite group obtained from
`B_f` by adjoining commuting involutions `u,v` which implement the two packet
flips `(SPF1)`.  Let `G` act transitively on `X=G/Gamma` as in
`compressor-fixed-site-growth-infinite`, and form the permutational wreath
group `W_f=H_f^(X) semidirect G`.

For every forbidden selector assignment `x`, `H_f` has a finite-dimensional
representation on `T_x tensor C^2` with

```text
pi_x(u)=Q_x tensor X,              pi_x(v)=P_x tensor Z,           (SFW2)
```

where the second Pauli pair cancels the packet anticommutation.  Use `pi_x`
at every site in the Bernoulli tensor representation.

For either strict positive compressor `s`, the difference
`s X^Gamma minus X^Gamma` contains infinitely many sites.  The local packet
algebras at any `n` distinct such sites are tensor independent and belong to
the compressed `Gamma`-relative commutant but not the original fixed-site
tensor algebra.  Their packet flip implementers have block-diagonal binary
projective commutator form with `n` symplectic blocks, hence rank `2n`.
Therefore one strict compressor step exposes Schur predicate holonomy of
arbitrarily large finite rank in the exact tracial wreath model.

This proves that exact completeness does not require a long recursion.  It
does not give a nonhyperlinear group: finite-microstate soundness still must
recover a number of individual site factors depending on the current matrix
multiplicity, with loss independent of that number.
No Connes-embeddability claim is made for the full Bernoulli crossed-product
trace.  What suffices for the local limitation is that every fixed finite
site tensor window is finite dimensional and therefore dilutable.
