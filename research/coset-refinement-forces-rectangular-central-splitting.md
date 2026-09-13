---
rg: 2
id: coset-refinement-forces-rectangular-central-splitting
kind: claim
title: A trace that factors through a coset refinement splits every question pair centrally into accepted rectangles
distinct_from:
  locally-affine-support-bcs-is-exactly-the-lcs-boundary: that is the elementary abelian case without padding, where the obstruction is the affine hull of the local support; this treats coset refinements over arbitrary finite groups with padded answers, and gives a group-independent necessary condition on the pair von Neumann algebras.
  coset-systems-are-torsor-isomorphism-games: that proves coset systems are torsor isomorphism games; this says which perfect traces of a given game can come from a coset system at all.
  jnvwy-active-output-has-no-affine-safe-perfect-model: that excludes affine-safe perfect models of one concrete verifier; this is a general firewall for coset refinements of any synchronous game.
---

**ESTABLISHED** by `coset-refinement-forces-rectangular-central-splitting-proof`.
Not reviewed by an ex-verify lane.

**Coset refinements.**  Let `G` be a finite synchronous game with answer sets
`A_q` and accepting sets `Acc_(qq') ⊆ A_q x A_(q')`.  A *coset refinement*
`R` of `G` consists of:

- finite groups `K_q` and maps `beta_q: K_q -> A_q` (padding is allowed);
- for each pair `q != q'`, a subgroup `D_(qq')` and an element `c_(qq')` with
  `(beta_q x beta_(q'))(c_(qq') D_(qq')) ⊆ Acc_(qq')`, transposed for `(q',q)`.

Its algebra `A(R)` is the coset-system algebra of
`coset-systems-are-torsor-isomorphism-games`.  The pushforward
`P_q^a = sum_(beta_q(s)=a) p_q^s` is a unital *-homomorphism `A(G) -> A(R)`.
So a tracial coset refinement of a game with no `R^U` model is a tracial,
non-`R^U` coset system, and by that node it gives a colored qc-but-not-qa pair.

**Theorem (RCS).**  Let `tau` be a tracial state on `A(R)`, let
`M = pi_tau(A(R))''`, and put `N_(qq') = W*(P_q, P_(q')) ⊆ M`.  For a
projection `f in M`, let `U_q(f) = {a : f P_q^a != 0}`.  Then for every pair
`q != q'` there are projections `f_1, ..., f_m` in the centre of `N_(qq')` with
`sum_j f_j = 1` and

```text
U_q(f_j) x U_(q')(f_j) ⊆ Acc_(qq')        for every j.                 (RCS)
```

In words: on each central piece, every answer used on `q` is accepted with
every answer used on `q'`.

**Corollaries.**

1. **Factor pairs.**  If `N_(qq')` is a factor, the whole used rectangle
   `U_q(1) x U_(q')(1)` lies in `Acc_(qq')`.
2. **Three-colourings.**
   - In a graph three-colouring game (`Acc = {(i,j) : i != j}` on edges),
     each central piece has disjoint nonempty used sets in `{1,2,3}`, so one
     of them is a singleton.  So the two PVMs commute on every piece.
   - Hence a trace that factors through a coset refinement has commuting
     PVMs on adjacent vertices.
   - Universal presentations by three-colouring games are therefore the wrong
     entry point for the torsor route.
3. **Label-matching presentations pass.**  If `Acc_(qq')` is itself a
   disjoint union of accepted rectangles, for example the "agree on shared
   variables" edges of a constraint-context game, the shared labels give
   (RCS) for every perfect model.  There the cost of the torsor route moves
   into lifting local answers to group elements.
4. **Without padding.**  Fix group structures `A_q = K_q` and
   `beta_q = id`.  Let `S_(qq') = {(a,a') : tau(P_q^a P_(q')^(a')) > 0}` be
   the support of a tracial state `tau` on `A(G)`, and pick any
   `s_0 in S_(qq')`.  Then `tau` factors through a coset refinement with these
   groups iff

   ```text
   s_0 < S_(qq')^(-1) S_(qq') >  ⊆  Acc_(qq')     for every pair,
   ```

   and this coset hull contains the rectangular (Mal'tsev) closure of
   `S_(qq')`, whatever the group structure.

**Model tests.**

- **A classical solution passes.**  `N_(qq') = C`, and the used rectangle is
  one accepted pair.
- **A real perfect model fails.**  Take two questions with answers
  `{1,2,3}` and `Acc = all pairs except (1,1)`, and work in `M_3` with its
  normalized trace.
  - Let `P_q` be the standard basis projections.
  - Let `P_(q')` be the basis projections of `f_1 = (e_2+e_3)/sqrt2` and
    `f_(2,3) = (e_1 ± (e_2-e_3)/sqrt2)/sqrt2`.
  - This is perfect, since `f_1 ⊥ e_1`.  The pair generates all of `M_3`, and
    the used rectangle contains `(1,1)`.
  - So this trace factors through no coset refinement.

**Scope.**

- (RCS) concerns the torsor syntax: square blocks that are left translations.
- A closure-safe square presentation whose fibres are not torsors is not
  covered (`closure-safe-support-is-exactly-the-colored-iso-rung`).
- For the independent-set sources, (RCS) applies to the pair algebras of the
  source game, by `independent-set-injection-splits-as-question-bijection`.
