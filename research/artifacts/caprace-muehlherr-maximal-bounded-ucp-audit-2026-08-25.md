# Caprace--Muehlherr maximal-bounded audit for the triangle ucp route

**Date:** 2026-08-25

**Source checked:** P.-E. Caprace and B. Muehlherr, *Isomorphisms of
Kac--Moody groups which preserve bounded subgroups*, Adv. Math. 206 (2006),
250--278.  Author PDF:
<https://perso.uclouvain.be/pierre-emmanuel.caprace/papers_pdf/KM2_bounded.pdf>.

The exact source facts used by
`group-word-tree-face-lift-classification-proof` are:

1. Corollary 3.8: for a finite-rank twin root datum with finite root groups
   and finite common torus, bounded subgroups are exactly finite subgroups.
2. Theorem 4.1, converse case `(i')`: the intersection of the stabilizers of
   two opposite maximal spherical residues is a maximal bounded subgroup.
3. Theorem 4.1, case `(i)`: such a maximal bounded subgroup stabilizes a
   unique maximal spherical residue in each half of the twin building.

For a maximal spherical rank-two subset `I` in a nonspherical rank-three
diagram, the standard finite Levi `L_I` is precisely the intersection in
item 2.  Items 1--2 therefore make it maximal finite.  Item 3 makes it
self-normalizing: a normalizer must preserve each singleton set of stabilized
residues, hence lies in their stabilizer intersection.  Distinct standard
rank-two subsets are nonconjugate because the group action on the building is
type-preserving and the stabilized residues are unique.

The paper states these results for the group with its twin root datum.  Passing
to the finite central quotient used by Caprace--Remy preserves maximal
finiteness, self-normalization, and nonconjugacy by taking full inverse images.
No assertion about arbitrary finite subgroups beyond these cited maximal
bounded results is used.
