---
rg: 2
id: sl3-prescribed-exact-relative-witnesses-do-not-exist
kind: claim
title: Every prime excludes relative SL3 witnesses with prescribed exact finite congruence lattice representatives
distinct_from:
  p-divisible-lambda-exact-mass-vanishes-at-large-primes: That gives a quantitative Clifford bound for primes at least eleven; this removes the small-prime restriction through exact positive orbit measures and allows arbitrary finite tracial coordinate algebras.
  sl3-re-lambda-exact-coprime-face-is-unfaithful: That excludes coprime-level exact matrix witnesses; this first removes every denominator-primary factor, at every prime and without conductor bounds, and also treats prescribed finite congruence images in general finite tracial coordinates.
  arithmetic-pair-is-not-relatively-embeddable: That is the unrestricted scalar relative-embedding target; this requires genuine finite congruence coordinate representatives of the lattice, a hypothesis not supplied for an arbitrary scalar witness.
artifacts:
  - research/artifacts/sl3-primary-exact-sector-kirillov-tightness-2026-09-08.md
  - research/artifacts/independent-kirillov-primary-sector-audit-2026-09-08.md
---

Fix any prime p and write C=SL_3(Z), A=SL_3(Z[1/p]), and
h=diag(p,1,p^-1). There is no data of the following form:

* finite tracial von Neumann algebras (M_n,tau_n) and unital
  von Neumann subalgebras B_n;
* a group homomorphism pi:A -> U(prod_omega M_n), represented by
  unitary coordinate maps U_n, with
  dist_2(U_n(c),B_n) ->_omega 0 for every c in C and
  ||E_(B_n)(U_n(a))||_2 ->_omega 0 for every a outside C;
* genuine homomorphisms sigma_n:C -> U(M_n), each factoring through
  some SL_3(Z/q_n), with [sigma_n(c)]=pi(c) for every c in C.

The canonical trace condition usually imposed on pi is unnecessary
for this exclusion. No restrictions are placed on q_n, dimensions,
conductor depths, isotypic multiplicities, or defect rates.
In particular this rules out every matrix relative witness of the
specified exact type and every Gao witness with prescribed exact
finite congruence lattice images, even in general QWEP coordinates.

The primary input proves the following stronger reduction. For any
genuine congruence sequence sigma_n and any unitary H_n satisfying
the h-overlap relations on a fixed Kazhdan set of
C intersect h^-1 C h with error tending to zero, write
q_n=p^(a_n)m_n with (p,m_n)=1. If rho_n is its CRT primary factor,
then

    sup_(k in SL_3(Z_p)) ||rho_n(k)-1||_2 ->_omega 0.

Thus sigma_n can be replaced uniformly on C by genuine
representatives of coprime level. This uses exact positive
Kirillov measures on fixed principal pro-p groups, an exact
large-corner intertwiner, and projective compactification.
The square-restriction form of the orbit method handles p=2.

The coprime congruence slot and uniform Kazhdan--Jones containment
then force ||E_(B_n)(U_n(h))||_2 ->_omega 1, contradicting h outside C.

This theorem does not exactify approximate lattice tuples.
Consequently it does not establish the unrestricted relative
nonembedding statement or existence of a nonhyperlinear group.
The earlier invalid constant-sequence algebra argument and invalid
metaplectic flux assemblies remain invalid; neither is used here.
