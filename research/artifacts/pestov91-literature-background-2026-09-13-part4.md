# Pestov 9.1: literature background, verified at source (part 4 of 4): yaml source rows

Lane `pc-lit-background`, 2026-09-13. Rows for the `sources:` section of `formalization.yaml`, in the format of the
Bowen–Chapman rows. Every quote and number below is verified in Parts 1–2. Integration notes:
- Three rows **replace** existing rows: Pestov, Ershov–Jaikin-Zapirain, Bekka–de la Harpe–Valette. Their
  Bowen–Chapman sentences are kept. The one wording change there is "of Gromov's theorem", so that "the converse" is
  not read as Pestov's Open question 3.4.
- The `original-proof` row for Pestov 9.1 belongs to pc-priority-credit and is not here.
- The Grigorchuk–Medynets, Clark–Edie-Michell and Jacobs–Keane notes describe the Lean chain as planned (ring LEF
  lane, `RingSimple.lean`, the period-doubling subshift). Check those notes against the landed modules.

```yaml
  # Background for the Pestov 9.1 result: where the question was printed and
  # where it came from, the definitions the challenge renders, the theorems
  # the witness uses or reproves, the literature that records the question as
  # open, and the nearest earlier objects. The row marked "other" is an input
  # this development proves in Lean rather than assumes.

  # REPLACES the existing Pestov row.
  - title: "Hyperlinear and sofic groups: a brief guide"
    authors: [Vladimir G. Pestov]
    year: 2008
    type: paper
    id: https://doi.org/10.2178/bsl/1231081461
    location: Open question 9.1
    relationship: background
    note: >-
      Bull. Symbolic Logic 14(4):449-480; arXiv:0804.3968v8, the version with
      the galley corrections. Section 9, page 21, prints the question answered
      by Palomar/comparator-pestov91.json: "Open question 9.1 (Cf. Ozawa [64]).
      Let G be an infinite simple group with Kazhdan's property (T). Can it be
      hyperlinear (sofic)?", as one of "The two candidates for a
      counter-example". Definitions 3.1 and 3.2 define sofic and hyperlinear
      groups as subgroups of metric ultraproducts of symmetric, respectively
      unitary, groups, Theorem 3.3 is Elek and Szabo's theorem that sofic
      groups are hyperlinear, and Theorem 3.6 is the unitary analogue of
      Theorem 3.5; the challenge's IsSoficGroup and IsHyperlinearGroup imply
      these two criteria. Theorem 3.5 is the textbook permutation definition
      of soficity, and section 6 surveys Gottschalk's surjunctivity conjecture
      and Gromov's theorem. The survey records only the forward implication of
      Gromov's theorem and does not pose the converse.

  - title: About the QWEP conjecture
    authors: [Narutaka Ozawa]
    year: 2004
    type: paper
    id: https://doi.org/10.1142/S0129167X04002417
    location: Section 7, after Theorem 7.4
    relationship: background
    note: >-
      Internat. J. Math. 15(5):501-530; arXiv:math/0306067v2, p. 26 (journal
      p. 527). The origin of the question, cited by Pestov as [64]: "It is
      unknown whether there exists a simple property (T) group Γ which is
      hyperlinear. By the above theorem, the full C*-algebra C*Γ of such a
      group Γ cannot have the LLP." Theorem 7.4 includes Kirchberg's theorem
      that a group with the properties (F) and (T) is residually finite. The
      second sentence is false for finite groups, whose full C*-algebras are
      finite-dimensional, so the question concerns infinite groups, as
      Pestov's wording makes explicit.

  - title: >-
      Discrete groups with Kazhdan's property T and factorization property are
      residually finite
    authors: [Eberhard Kirchberg]
    year: 1994
    type: paper
    id: https://doi.org/10.1007/BF01459798
    location: Theorem 1.1
    relationship: background
    note: >-
      Math. Ann. 299:551-563. "A discrete group with property (F) and property
      T is residually finite" (p. 552). An infinite simple group is not
      residually finite, so an infinite simple Kazhdan group does not have the
      factorization property, which is the fact behind Ozawa's remark. Item
      (v) of Corollary 1.2, on almost connected locally compact groups, is
      disproved by Thom (arXiv:0810.2180, Remark 1.6) and is not used.

  - title: Examples of hyperlinear groups without factorization property
    authors: [Andreas Thom]
    year: 2010
    type: paper
    id: https://doi.org/10.4171/GGD/80
    location: Theorem 1.4
    relationship: background
    note: >-
      Groups Geom. Dyn. 4(1):195-208; arXiv:0810.2180v1, p. 4. The nearest
      earlier object: "There exists a finitely generated Kazhdan group G which
      is locally embeddable into finite groups (in particular sofic and hence
      hyperlinear) but does not have the factorization property." The group
      is non-hopfian, so it is not simple. Page 3 names the two known sources
      of simple Kazhdan groups, lattices in Kac-Moody groups and Gromov's
      Tarski monster quotients of hyperbolic Kazhdan groups.

  # REPLACES the existing Ershov-Jaikin-Zapirain row.
  - title: Property (T) for noncommutative universal lattices
    authors: [Mikhail Ershov, Andrei Jaikin-Zapirain]
    year: 2010
    type: paper
    id: https://doi.org/10.1007/s00222-009-0218-2
    location: Theorem 1.1
    relationship: other
    note: >-
      Invent. Math. 179(2):303-347; arXiv:0809.4095v2. Property (T) for
      elementary groups of rank at least three over finitely generated rings,
      which is what gives both groups of the Bowen-Chapman pair property (T),
      and what gives property (T) to EL_3 of the crossed-product ring of the
      Pestov 9.1 witness and to its quotients. Before it, property (T) for
      EL_n(R), n at least 3, was known when R is commutative or has stable
      range at most n. Proved in this development.

  # REPLACES the existing Bekka-de la Harpe-Valette row.
  - title: "Kazhdan's Property (T)"
    authors: [Bachir Bekka, Pierre de la Harpe, Alain Valette]
    year: 2008
    type: book
    id: https://doi.org/10.1017/CBO9780511542749
    location: Definition 1.1.3, Example 1.7.4 and Proposition 1.7.6
    relationship: background
    note: >-
      New Mathematical Monographs 11, Cambridge University Press. Property (T)
      for SL_d of the integers and its stability under extensions, which is
      what Kun and Thom use to make the semidirect product Kazhdan. This
      development proves its own semidirect-product theorem instead.
      Definition 1.1.3 is the Kazhdan pair that Palomar/Pestov91Challenge.lean
      renders for a discrete group, whose compact Kazhdan sets are the finite
      ones: every unitary representation with a (Q, ε)-invariant vector, in
      the strict sense of Definition 1.1.1, has a non-zero invariant vector.

  - title: On algebraic properties of topological full groups
    authors: [Rostislav Grigorchuk, Konstantin Medynets]
    year: 2014
    type: paper
    id: https://doi.org/10.1070/SM2014v205n06ABEH004400
    location: Definition 2.5 and Theorem 2.6
    relationship: background
    note: >-
      Sb. Math. 205(6):843-861; arXiv:1105.0719v4, p. 5. "The topological full
      group of any Cantor minimal system is an LEF group", proved by periodic
      approximation of the system. The Pestov 9.1 witness is made LEF by the
      same mechanism applied to a ring: periodic words of the subshift give
      matrix models over F_2 of the crossed product. That ring version is
      proved in this development, and the theorem on topological full groups
      is not used.

  - title: Simplicity of algebras associated to étale groupoids
    authors: [Jonathan H. Brown, Lisa Orloff Clark, Cynthia Farthing, Aidan Sims]
    year: 2014
    type: paper
    id: https://doi.org/10.1007/s00233-013-9546-z
    location: Theorem 4.1
    relationship: background
    note: >-
      Semigroup Forum 88(2):433-452; arXiv:1204.3127v2. The complex Steinberg
      algebra of a locally compact Hausdorff étale groupoid with totally
      disconnected unit space is simple if and only if the groupoid is
      effective and minimal. The theorem is stated over the complex numbers;
      the versions over an arbitrary field are the next two rows.

  - title: Uniqueness theorems for Steinberg algebras
    authors: [Lisa Orloff Clark, Cain Edie-Michell]
    year: 2015
    type: paper
    id: https://doi.org/10.1007/s10468-015-9522-2
    location: Corollary 4.6
    relationship: background
    note: >-
      Algebr. Represent. Theory 18(4):907-916; arXiv:1403.4684v1, p. 7. "Let G
      be a Hausdorff, ample groupoid and R a commutative ring with identity.
      Then A_R(G) is simple if and only if G is effective and minimal, and R
      is a field." The witness ring LC(X, F_2) ⋊ Z is the Steinberg algebra
      over F_2 of the transformation groupoid of the shift on X, which is
      effective, because the action is free, and minimal. The development
      proves the ring simple directly (GroupApproximation/Pestov91/RingSimple.lean).

  - title: >-
      Simplicity, primitivity and semiprimitivity of étale groupoid algebras
      with applications to inverse semigroup algebras
    authors: [Benjamin Steinberg]
    year: 2016
    type: paper
    id: https://doi.org/10.1016/j.jpaa.2015.08.006
    location: Corollary 3.6
    relationship: background
    note: >-
      J. Pure Appl. Algebra 220(3):1035-1054; arXiv:1408.6014v2, p. 10. "Let G
      be a Hausdorff ample groupoid and k a field. Then kG is simple if and
      only if G is effective and minimal." An independent field-general form
      of the same criterion.

  - title: Obstructions to matricial stability of discrete groups and almost flat K-theory
    authors: [Marius Dadarlat]
    year: 2021
    type: paper
    id: https://doi.org/10.1016/j.aim.2021.107722
    location: Proposition 3.19
    relationship: background
    note: >-
      Adv. Math. 384:107722; arXiv:2007.12655v2. Proposition 3.19
      (Ozawa-Thom): "If an infinite property (T) group G is weakly
      quasidiagonal, then G has an infinite residually finite quotient", so
      infinite simple Kazhdan groups are not weakly quasidiagonal (Example
      3.15(ii)). The introduction (p. 2) also prints "It is clear from
      definitions that MF ⇒ weak quasidiagonality". LEF groups are MF, so with
      Proposition 3.19 the Pestov 9.1 witness shows that this clause fails for
      groups. That consequence is not formalized, and the journal text was not
      compared with arXiv v2.

  - title: An introduction to hyperlinear and sofic groups
    authors: [Vladimir G. Pestov, Aleksandra Kwiatkowska]
    year: 2012
    type: paper
    id: https://doi.org/10.1017/CBO9781139208574.006
    location: Section 10
    relationship: background
    note: >-
      In Appalachian Set Theory 2006-2012, edited by James Cummings and Ernest
      Schimmerling, Cambridge University Press, pages 145-186;
      arXiv:0911.4266v4, p. 28. Records the question as open after Thom's
      example: "a hope to use property (T) in order to construct
      non-hyperlinear groups is a bit diminished now, but surely not gone, as
      it remains in particular unknown whether finitely generated simple
      Kazhdan groups can be hyperlinear/sofic."

  - title: Introduction to Sofic and Hyperlinear Groups and Connes' Embedding Conjecture
    authors: [Valerio Capraro, Martino Lupini]
    year: 2015
    type: book
    id: https://doi.org/10.1007/978-3-319-19333-5
    relationship: background
    note: >-
      Lecture Notes in Mathematics, Springer; arXiv:1309.2034v6. The textbook
      survey of sofic and hyperlinear groups after Pestov's guide. A search of
      its source finds property (T) only in the definition, in a residually
      finite hyperbolic Kazhdan group, in de Cornulier's finitely presented
      non-Hopfian Kazhdan group, which is not LEA, and in II_1 factors; it
      does not state Question 9.1.

  - title: A sofic group away from amenable groups
    authors: [Yves Cornulier]
    year: 2011
    type: paper
    id: https://doi.org/10.1007/s00208-010-0557-8
    location: Section 1
    relationship: background
    note: >-
      Math. Ann. 350(2):269-275; arXiv:0906.3374v2, p. 2. Records the soficity
      of some Kazhdan groups as open: "examples of infinite isolated groups
      with Kazhdan's Property T were given [CGP, Paragraph 5.4], but it is not
      known if they are sofic." Those groups are not said to be simple, and
      the Pestov 9.1 witness does not bear on them.

  - title: Centralizers of sofic approximations of Kazhdan groups
    authors: [Vadim Alekseev, Andreas Thom]
    year: 2026
    type: paper
    id: https://arxiv.org/abs/2608.05362
    location: Section 5 and Open problem 6.1
    relationship: background
    note: >-
      v1, 2026-08-05. A Kazhdan group admitting a sofic embedding whose
      centralizer acts ergodically is LEF, and residually finite if finitely
      presented. Section 5 reviews the known sofic Kazhdan groups that are not
      residually finite, Thom's LEF example, and names no simple one. Open
      problem 6.1 asks: "Are there examples of finitely presented sofic groups
      with Kazhdan's property (T) that are not residually finite?" The Pestov
      9.1 witness is LEF and not finitely presented, so it agrees with their
      theorem and leaves 6.1 open.

  - title: Simplicity and superrigidity of twin building lattices
    authors: [Pierre-Emmanuel Caprace, Bertrand Rémy]
    year: 2009
    type: paper
    id: https://doi.org/10.1007/s00222-008-0162-6
    relationship: background
    note: >-
      Invent. Math. 176(1):169-221; arXiv:math/0607664v2. Twin building
      lattices are simple if and only if the buildings are irreducible and not
      of affine type, and "many of them are finitely presented and enjoy
      property (T)": the first source of simple Kazhdan groups that Thom names.
      A finitely presented LEF group is residually finite, so the finitely
      presented ones are not LEF.

  - title: Hyperbolic groups
    authors: [Misha Gromov]
    year: 1987
    type: paper
    id: https://doi.org/10.1007/978-1-4613-9586-7_3
    relationship: background
    note: >-
      Essays in Group Theory, MSRI Publications 8, Springer, 75-263. Infinite
      simple Kazhdan groups as quotients of hyperbolic Kazhdan groups, cited by
      Ozawa and by Pestov ([37]: "For a way to construct groups with a
      combination of properties mentioned in Problem 9.1") and recalled by
      Thom (arXiv:0810.2180, p. 3).

  - title: "Hyperlinearity, essentially free actions and L2-invariants. The sofic property"
    authors: [Gabor Elek, Endre Szabo]
    year: 2005
    type: paper
    id: https://doi.org/10.1007/s00208-005-0640-8
    location: Theorem 2
    relationship: background
    note: >-
      Math. Ann. 332(2):421-441. "We shall prove that countable sofic groups
      are hyperlinear (Theorem 2)" (p. 423), and "It is known [8],[19],[6]
      that the LEF-groups are sofic" (p. 422). Both implications are proved in
      this development for arbitrary groups in the finite-set forms,
      GroupApproximation.isSofic_of_isLEF and
      GroupApproximation.isHyperlinear_of_isSofic.

  - title: Groups that are locally embeddable in the class of finite groups
    authors: [A. M. Vershik, E. I. Gordon]
    year: 1998
    type: paper
    relationship: background
    note: >-
      St. Petersburg Math. J. 9:49-67. The reference for LEF groups given by
      Grigorchuk and Medynets (arXiv:1105.0719, p. 5), who credit the notion to
      Vershik and Stepin in the 1980s.

  - title: 0-1-sequences of Toeplitz type
    authors: [Konrad Jacobs, Michael Keane]
    year: 1969
    type: paper
    id: https://doi.org/10.1007/BF00537017
    relationship: background
    note: >-
      Z. Wahrscheinlichkeitstheorie verw. Gebiete 13:123-131. Introduces
      Toeplitz sequences, "constructed by successive insertion of a periodic
      sequence of symbols 0, 1 and "hole" into the "holes" of the sequence
      already constructed", and proves them almost periodic (Theorem 4). The
      Pestov 9.1 witness is built on the orbit closure of the period-doubling
      sequence, the parity of the 2-adic valuation of n, and this development
      proves its minimality and aperiodicity directly.
```
