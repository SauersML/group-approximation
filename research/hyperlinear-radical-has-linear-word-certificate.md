---
rg: 2
id: hyperlinear-radical-has-linear-word-certificate
kind: claim
title: A hyperlinear-radical word is exactly a finite ordinary HS energy domination certificate
distinct_from:
  hyperlinear-radical-presentation-compactness: that permits a different finite relator window for every tolerance; this yields one fixed finite list and one positive integer multiplying the sum of squared ordinary HS defects.
  hyperlinear-radical-is-finitely-witnessed: that produces a finite-prefix radical witness; this gives a global scalar-sensitive linear energy inequality on its bare matrix tuples.
  character-domination-collapse-equivalences: that uses projective character defects; this controls the ordinary distance from the identity, including scalar phases, for a word in a presented group.
  fixed-hs-word-gap-is-linear-domination: that linearizes an assumed fixed gap for arbitrary word lists; this identifies its hypothesis with actual radical membership via presentation compactness.
artifacts:
  - research/artifacts/hyperlinear-word-certificate-2026-09-07.md
  - research/artifacts/hs-word-certificate-rational-search.md
---

Let Gamma=<S|r_1,r_2,...> have finitely many generators and a finite or
countable relator list, with no effectiveness assumption. For w in F(S),
membership of wbar in Rad_hyp(Gamma) is equivalent to the existence of a
finite sublist R_0 and an integer N>=1 such that

```text
||w(U)-I||_(2,d)^2 <= N sum_(r in R_0)||r(U)-I||_(2,d)^2
```

for every d>=1 and every U in U(d)^S. For a finite presentation one can
take the whole relator list. The window and integer are not claimed
computable, and no nontrivial instance is supplied.

If wbar!=1, any actual certificate supplies the finitely presented
nonhyperlinear witness <S|R_0>. For an infinite simple finitely presented
group and a fixed nontrivial word, this certificate exists if and only
if the group is nonhyperlinear.

For a specified finite R_0, word w and rational coefficient, failure of
the proposed inequality is uniformly semidecidable, by
`failed-hs-word-bounds-have-rational-witnesses`. Its strict counterexamples
can be replayed on exactly unitary Q(i) matrices. Thus validity of a fixed
coefficient is a Pi-zero-one condition. A bounded search with no
counterexample does not establish that condition or radical membership.
