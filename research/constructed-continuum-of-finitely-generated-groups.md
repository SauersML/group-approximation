---
rg: 2
id: constructed-continuum-of-finitely-generated-groups
kind: claim
title: A constructed continuum of pairwise nonisomorphic finitely generated groups
distinct_from:
  continuum-nonisomorphic-fg-non-mf: That is the statement about non-MF groups and consumes this one; this is a pure group-theory statement with no approximation property in it, and is what replaces the external citation to B. H. Neumann.
  continuum-nonisomorphic-non-mf-cylinder: That asks for continuum many isomorphism types inside the literal clopen cylinder of marked quotients of E; the groups here are alternating lamplighters over free-group coset spaces and have nothing to do with that cylinder.
artifacts:
  - GroupApproximation/Monsters/NeumannAlternatingFamily.lean
  - GroupApproximation/Monsters/NeumannNormalSubgroups.lean
  - GroupApproximation/Monsters/NeumannContinuum.lean
  - GroupApproximation/Sofic/ContinuumFamilyCriterion.lean
  - GroupApproximation/Sofic/ContinuumFromNormalSubgroups.lean
---

ESTABLISHED, and *constructed* rather than quoted.
`Monsters.NeumannContinuum.neumann_continuum_of_finitely_generated_groups`:
there is a family of finitely generated groups indexed by a set of cardinality
`2^{aleph_0}`, pairwise nonisomorphic.

The family is not B. H. Neumann's.  For `S subseteq N` put

    W S  =  A5 wreath_{F2 / markedSubgroup S} F2,

the permutational wreath product of the alternating group `A5` over the coset
space of `markedSubgroup S = <a^n b a^{-n} : n in S>` inside the free group
`F2`.  Each `W S` is finitely generated -- `F2` acts transitively on the coset
space, so the two free generators and the sixty one-site lamps at the base
coset suffice -- and the subgroups `markedSubgroup S` are pairwise distinct,
because in the lamplighter picture `a^n b a^{-n}` is the one-site lamp at the
site `a^n`.

## Why the members are separated by counting, not by an invariant

Distinct subgroups need not give nonisomorphic wreath products -- conjugate
subgroups give isomorphic ones -- so the family is separated the way the
manuscript's own paragraph separates its products: for a fixed countable `Q`
only countably many `H` satisfy `W H =~ Q`, and a map with countable fibres
from a continuum-sized domain has continuum-sized image.  A transversal of the
isomorphism classes is the family asserted here.

`Sofic/ContinuumFamilyCriterion` had reduced the obligation to "a family
indexed by subsets of `N` with an isomorphism invariant recovering the subset",
which is the shape every known construction produces; this construction does
not use that economy -- it separates by counting -- and
`manuscriptContinuumMultiplicityFromCriterion` discharges the criterion anyway
by transporting the transversal along a bijection with the powerset of `N`.

## The counting lemma that made it cheap

`Sofic/ContinuumFromNormalSubgroups` removes the hard half of Neumann's
theorem: a normal subgroup with a *prescribed* quotient is the kernel of an
epimorphism, an epimorphism out of a finitely generated group is determined by
its values on a finite generating set, so for a fixed quotient there are only
countably many such normal subgroups.  Hence "normal subgroup |-> isomorphism
type of the quotient" has countable fibres, and no isomorphism invariant has to
be exhibited at all.  Neumann's own invariant -- the set of alternating groups
occurring as minimal normal subgroups, needing two-generation of `A_n` by a
3-cycle and an n-cycle plus a support-separation argument -- is not needed.
