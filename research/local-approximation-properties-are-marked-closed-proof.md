---
rg: 2
id: local-approximation-properties-are-marked-closed-proof
kind: route
title: Transport a failing finite table along ball isomorphisms and along the finite truncation
target: local-approximation-properties-are-marked-closed
requires: []
---

Write `P = P_M`.

**1, 2.**  If `H <= G` and `F <= H` is finite then `tab_H(F) = tab_G(F)`, so
`P(G)` gives `P(H)`.  Isomorphisms carry tables to isomorphic tables.  A
finite subset of a directed union lies in one member, and a finite subset of
`G` generates a finitely generated subgroup containing it, which gives
locality.

**3.**  Suppose `G = <X | N>` fails `P`: fix a finite `F <= G` and `eps > 0`
with `not M(tab_G(F), eps)`.  Choose a word `w_x` of length `<= r` for every
`x in F u F.F`, and put `R = 4r`.  Let `G'` be a marked group on `X` such
that a word of length `<= R` is trivial in `G'` iff it is trivial in `G`.
Then for words `u, v` of length `<= 2r`, `u = v` in `G'` iff `u = v` in `G`
(apply the hypothesis to `u^-1 v`).  Hence `x |-> [w_x]_{G'}` is injective on
`F u F.F`, and for `x, y in F` the equality `w_x w_y = w_{xy}` (length
`<= 3r`) transfers from `G` to `G'`.  So the image `F'` of `F` in `G'` has
`tab_{G'}(F') ~= tab_G(F)`, whence `not M(tab_{G'}(F'), eps)` and `G'` fails
`P`.  This is precisely openness of the failure locus in the marked-group
topology.

**4.**  With `F`, `eps`, `w_x` as above, each of the finitely many word
equalities `w_x w_y = w_{xy}` (`x, y in F`) holds in `G`, hence is a
consequence of finitely many relators of `N`.  Let `N_0 <= N` be a finite set
of relators from which all of them follow and put `G^ = <X | N_0>`.  Since
`N_0 <= N`, the identity on `X` induces an epimorphism `G^ -> G`.  In `G^`
the equalities hold by construction, and the inequalities `w_x != w_y`
(`x != y`) hold because they hold in the quotient `G`.  Thus the image `F^`
of `F` in `G^` satisfies `tab_{G^}(F^) ~= tab_G(F)`, so `G^` fails `P`, and
`G^` is finitely presented.

**5.**  Given the finite obstruction and the finitely many equalities,
enumerate the consequences of `N` until every equality has a derivation; the
relators used form `N_0`.  Only the *search for* the obstruction is
non-effective, which is what the recognition results measure.

The sofic case is `Covers.TableCover` verbatim: `TableModel G F eps` is the
model predicate, `exists_table_obstruction` is the failing `(F, eps)`, and
`tableGroup_not_isSofic` is step 4.  The hyperlinear case is separately
machine-checked in `Covers.HyperlinearTableCover`: the conditional naming map
pulls any finite unitary model of `tableTestSet` back to the original table,
and `exists_finitelyPresented_cover_of_not_isHyperlinear` enlarges the
obstruction by a finite generating set so that `tableEvaluation` remains
surjective.
