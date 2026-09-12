# Source verification: (L)LP permanence inputs — 2026-08-21

Both PDFs fetched and read at proof level this date.

## Enders–Shulman, *On the (Local) Lifting Property*, arXiv:2403.12224

Note the paper is by Dominic Enders and Tatiana Shulman (an earlier graph
annotation attributed the arXiv id to Pisier; Pisier is their [33]/[34],
the plain free-product LLP theorem quoted as Corollary 3.6).

- **Definition 2.1/2.2 (verbatim in substance).**  A ccp map
  `phi : A -> B/I` is liftable if it factors through a ccp `A -> B`;
  locally liftable if for every finite-dimensional operator system
  `E c A` the restriction `phi|_E` lifts.  A unital `A` has the LP
  (resp. LLP) if every ccp map from `A` into *any* quotient C*-algebra
  `B/I` is liftable (resp. locally liftable).
- **Theorem 3.4.**  Characterization of the LLP by lifting
  *-homomorphisms `A -> M(D (x) K)` up to a direct-sum correction `g`
  (`f (+) g` lifts to a *-homomorphism into `M(pi^{-1}(D) (x) K)`).
- **Lemma 4.1.**  `F` finite-dimensional, `alpha, beta : F -> B` unital
  *-homomorphisms with `alpha(p) ~ beta(p)` (Murray–von Neumann) for
  all projections `p in F`: then `alpha, beta` are unitarily
  equivalent, by a unitary `U = sum_k sum_j beta(e_j1^(k)) v_k
  alpha(e_1j^(k))` built from finitely many partial isometries `v_k`
  matching the minimal projections of the matrix summands of `F`;
  part (ii) refines `U` to `pi(U) = 1` when all `alpha(p) ~ 1 ~
  beta(p)` and the unitary group of `B/I` is connected.
- **Theorem 4.2.**  `F` finite-dimensional in unital `A, B`;
  `f_A, f_B` into `M(D/I (x) K)` agreeing on `F`, each liftable after
  a direct-sum correction: then the corrections can be modified so
  that the two lifts *agree on `F` exactly* (pad by
  infinite-multiplicity faithful representations to make every
  `F`-projection equivalent to 1, then two conjugations via Lemma
  4.1).  The glued lift is a *-homomorphism on `A *_F B` by the
  universal property of the amalgam.
- **Corollary 4.3.**  `A, B` separable with LP, `F` finite-dimensional:
  `A *_F B` has the LP.  (New; answers Ozawa's question [31, p. 15].)
- **Corollary 4.5 (attributed by the authors to Ozawa [31]).**  `A, B`
  separable with LLP: `A *_F B` has the LLP, `F` finite-dimensional.
- **Corollary 4.6 (verbatim).**  "Let G be a finite tree product with
  finite edge groups.  For a vertex v, let G_v denote the
  corresponding vertex group.  If for each vertex v, C*(G_v) has the
  LP, then C*(G) has the LP.  In particular, if G is a finitely
  generated virtually free group, then C*(G) has the LP."
- Their introduction records Choi–Effros: nuclear (in particular
  finite-dimensional) C*-algebras have the LP.

## Fournier-Facio–Willett, arXiv:2603.18456v2

- **Theorem 1.2.**  LP + property FD for: (i) `pi_1` of manifolds of
  dimension `<= 3`; (ii) virtually free-by-cyclic groups; (iii)
  certain one-relator groups; (iv) limit groups; (v) RAAGs on chordal
  graphs.  All such groups are very flexibly stable.
- **Corollary 4.1.**  "A virtually LLP group is LLP.  A countable
  virtually LP group [is LP]."
- **Example 4.30.**  Their chordal-RAAG proof: chordal defining graph
  iff the derived subgroup is free (Servatius–Droms–Servatius [174,
  Theorem 2]), then LP by their Corollary 4.6 (groups with `Gamma^(n)`
  free).  NOT a clique-tree amalgam induction.
- **Remark 4.31.**  RACGs on chordal graphs are virtually free, hence
  LP.
- **Question 1.6.**  "Does `F_2 x F_2` have the (L)LP?"  Verbatim from
  the surrounding discussion: "The presence of `F_2 x F_2` subgroups
  is therefore a significant obstacle for generalizing the (L)LP to
  right-angled Artin groups beyond the chordal case."
- **Question 1.7.**  RAAGs with no induced squares: (L)LP?  (R)FD?
  "The first non-chordal example is the pentagon, for which we already
  do not know the answer."

## Lohrey–Sénizergues, *When Is a Graph Product of Groups
Virtually-Free?*, Comm. Algebra 35 (2007), no. 2, 617–621

PDF not reachable this date (author's copy 301s to a dead page;
publisher 403s).  Verified: title, venue, year via the publisher's
listing, and the finite-vertex-group direction as indexed from the
author's copy: a graph product of finite groups over a chordal graph
is virtually free.  The graph therefore cites this paper at
title/statement level ONLY and carries its own self-contained proof of
everything it uses
(`chordal-finite-graph-products-virtually-free-proof`).
