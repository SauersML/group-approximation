---
rg: 2
id: some-countable-group-factor-is-locally-universal
kind: claim
title: Some countable group has a locally universal group von Neumann algebra
distinct_from:
  non-ru-bcs-is-satisfiable-in-a-group-factor: that asks for one exact model of the non-RU constraint system in some group factor; this asks that every separable tracial von Neumann algebra embed in an ultrapower of one fixed group factor, which yields ultrapower-level models of that system but not exact ones.
  locally-universal-group-factor-group-is-nonhyperlinear: that is the implication from local universality to non-hyperlinearity; this is the existence statement it consumes.
---

**OPEN.**  There is a countable discrete group `U` such that every separable
tracial von Neumann algebra embeds, unitally and trace-preservingly, into an
ultrapower of `L(U)`.

By `locally-universal-group-factor-group-is-nonhyperlinear` any such `U` is
non-hyperlinear, so this is a strengthening of `non-hyperlinear-group`.  No
converse is known.

**Known constraints.**
- `computable-groups-have-no-locally-universal-group-factor`: `U` is not a
  computable group; a finitely generated witness has unsolvable word problem
  (conditional on the imported Arulseelan--Manzoor theorem).
- `group-factor-local-universality-reduces-to-ultraproducts`: existence is
  equivalent to the class statement that every separable tracial von Neumann
  algebra embeds in some ultraproduct of group von Neumann algebras of
  countable groups.  Only non-Connes-embeddable algebras carry content, since
  every II_1 group factor already contains `R`.

## Attempts

1. **Higman's universal finitely presented group, or the free product of all
   finitely presented groups (2026-09-13, lane solve-nh-locally-universal).**
   *Not decided.*  Such `U` contain every recursively presented group, but
   containing groups is not the issue: local universality needs the moment
   tables of every non-RU constraint algebra to be approximately realized by
   contractions in `L(U)`, and nothing forces these contractions to be
   approximated by group elements.  For finitely presented witnesses the
   necessary condition above adds that the word problem is unsolvable, which
   Higman's universal group satisfies; so the computability filter does not
   exclude it.
2. **Free products of solution groups of all linear-system games (idea file
   approach 4).**  *Not decided; the computability filter does not apply.*  A
   countable free product is computable only when its factors are uniformly
   computable, and that fails as soon as one solution group has unsolvable word
   problem.  The real obstruction is the one recorded on
   `mipstar-bcs-tracial-nonru-exists`: the non-RU separation is known for
   Boolean constraint systems, and transferring it to linear systems (hence to
   group factors) is Paddock--Slofstra's open boundary.
