---
rg: 2
id: amenable-fp-double-coset-cover-is-pi2-hard
kind: claim
title: Some computable family of amenable finite presentations is covered by three listed double cosets exactly on the total indices
distinct_from:
  amenability-of-finite-presentations-is-pi2-complete: that asks for any Pi-zero-two hard family of finite presentations with amenable positive branch; this asks for a combinatorial cover event inside amenable groups. By commuting-conjugate-switch-amenability-criterion it implies the root, and no converse is known.
  finitely-generated-centralizer-switches-are-sigma1: that shows the generation event K = C is Sigma-zero-one; this asks for the double-coset cover event K = C cup CUC cup CU^-1C to be Pi-zero-two hard, which needs subgroups of infinite index.
  finite-bi-index-forces-finite-index-in-metabelian-groups: that screens out virtually polycyclic and abelian-by-virtually-abelian ambients; this is the hardness statement that must be realised outside those classes.
---

**OPEN.**

## Statement

There is a computable map `e -> (K_e, S_e, U_e)` with the following properties.

- `K_e = <X_e | R_e>` is a finite presentation of an amenable group.
- `S_e` and `U_e` are finite sets of words in `X_e`, and `C_e = <S_e>`.
- `e in TOT` iff `K_e = C_e cup C_e U_e C_e cup C_e U_e^-1 C_e`.

By `commuting-conjugate-switch-amenability-criterion`, the finite presentations
`Q_e = <X_e, b | R_e, [b,s] (s in S_e), [b, u b u^-1] (u in U_e)>` then reduce
`TOT` to `AMENABLE_fp`. On total indices, `Q_e = Z wr_(K_e/C_e) K_e`.

The weaker hypothesis "`K_e` is amenable for `e in TOT`" would also suffice,
because a non-amenable `K_e` already makes `Q_e` non-amenable.

## Necessary features

1. **Infinite index.** The set of total `e` with `|K_e : C_e| < infinity` is
   contained in the c.e. set of indices that have a finite coset-table
   certificate. That c.e. set is a subset of `TOT`. Since `TOT` is not c.e.,
   infinitely many total `e`, in fact a non-c.e. set of them, need `C_e` of
   infinite index and finite bi-index.
2. **Ambient class.** On those indices `K_e` is neither virtually polycyclic nor
   abelian-by-virtually-abelian, by
   `finite-bi-index-forces-finite-index-in-metabelian-groups`.
3. **Finite rank.** On the total indices of item 1 where `C_e` has infinite
   index, `K_e/C_e` is an infinite transitive `K_e`-set of rank at most
   `1 + 2|U_e|` with finitely generated stabilizer. The positive witness
   `Z wr_(K_e/C_e) K_e = Q_e` is then a finitely presented amenable permutational
   wreath product with infinite base set. So `K_e` is a finitely presented amenable
   group without Cornulier's Property (LBF): some finitely generated subgroup of
   finite bi-index has infinite index (arXiv:math/0509090v2, Definition 3.11).
   Cornulier's Question 3.24(2), whether a finitely presented *solvable* group
   without (LBF) exists, was open there (2006). A solvable hole family would
   settle it.

## Attempts

1. **Polycyclic and metabelian ambients, including the finitely presented
   metabelian groups.** These are dead. Finite bi-index forces finite index, and
   the locus becomes `Sigma^0_1` (`finite-bi-index-metabelian-proof`).
2. **Houghton ambients `H_n`, `n >= 3`.** These are elementary amenable, and the
   natural action has rank two with point stabilizer isomorphic to `H_n`. So they
   supply finitely presented amenable positive instances `Z wr_X H_n`. Finite
   presentation of `H_n` (`n >= 3`), elementary amenability, and the stabilizer
   isomorphism are stated in Cornulier, arXiv:math/0509090v2, Example 3.6, which
   cites K. S. Brown (1987). Brown's paper itself was not fetched.
   They die for encoding: the group is fixed, its rank is fixed, and the word
   problem is solvable. A family needs ambients whose rank depends on a
   computation.
3. **Wreath lift of a machine group.** Take `K = M wr_X H` with `H` highly
   transitive, acting on `X x M/P`. Its rank is `1 + |P\M/P|`, so the cover
   problem returns to the bi-index of `P` in the machine group `M` itself.
   *No gain.* (Artifact, Section 5.3.)
4. **KMS machine groups in `A_p^2 A`,** as used for `RF_fp`.
   - By the orbit-module argument, an infinite finite-rank transitive action
     would need an infinite simple `F_p[R]`-module with finitely many `R`-orbits,
     for some finitely generated metabelian `R`. Without the simplicity and
     characteristic refinements, this is Cornulier's Proposition 3.23 for
     `n = 3` (arXiv:math/0509090v2), where the question is left open (Question
     3.24(1)).
   - Neither a construction nor an exclusion is known. The commutative field
     argument of the metabelian screen does not apply to `F_p[R]`.
   - In the KMS class itself, `R` lies in `A_p A`. The module must then have no
     nonzero fixed vector of `B`, where `B` is the elementary abelian normal
     `p`-subgroup of `R` with `R/B` abelian. If it
     had one, `B` would act trivially and the commutative field argument would
     apply. Also, some `B`-orbit must be infinite, and the stabilizers `B_v`
     must be proper subgroups in finitely many `R`-conjugacy classes whose
     conjugates contain arbitrarily large finite subgroups of `B`. These are
     proved in artifact Section 5.1.
   - These constraints do not exclude the class. `C_c^infty(F_p((t)), F_p)`,
     under `C_p wr Z` acting by `x -> t^j x + b` with `b in F_p[t, t^-1]`, is an
     infinite simple module with no base-fixed vector. It still has infinitely
     many orbits, because the ratio of diameter to ball radius of supports is a
     similarity invariant (artifact Section 5.1).
   - Infinite simple modules do exist, for example modules induced from a
     character of the base of `Z wr Z`, which is outside `A_p A`. Suppose a
     module restricted to an abelian normal base is semisimple with infinitely
     many isotypic components. Then it has infinitely many orbits, because the
     number of components in a vector's support is invariant.
     This is recorded in the swarm notes of 2026-09-16.
   - *Open*; this is the first class-three test case (artifact, Section 5.1).
5. **Thompson's group `F`.** It acts on the dyadic points of `(0,1)` with rank
   three. It is transitive on pairs `a < b` (Cornulier, arXiv:math/0509090v2,
   Example 3.4; not re-derived here). It is unusable while
   `thompson-f-is-amenable` is open, and it is a single group.
