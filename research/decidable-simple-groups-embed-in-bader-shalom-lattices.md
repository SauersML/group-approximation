---
rg: 2
id: decidable-simple-groups-embed-in-bader-shalom-lattices
kind: claim
title: Every infinite finitely generated simple group with solvable word problem embeds in a cocompact lattice with dense projections in a product of two just-non-compact groups
distinct_from:
  bader-shalom-normal-subgroup-theorem: that is the established normal subgroup theorem for such lattices; this is the open universality statement that every decidable simple group lies in one of them.
  boone-higman-iff-fp-just-infinite-hosts: that is the established equivalence with finitely presented just-infinite hosts; this is a specific, independently falsifiable source of just-infinite hosts, with no finite presentation demanded.
  burger-mozes-infinitely-transitive-tree-groups: that imports lattices in products of two trees, into which Burger-Mozes embed the fundamental groups of VH-T-complexes; this asks for embeddings of arbitrary decidable simple groups, and the Haagerup obstruction recorded below rules out tree factors on both sides.
---

**OPEN.**

Let `S` be an infinite finitely generated simple group with solvable word problem.
Then there exist `G_1`, `G_2` and a lattice `Γ` such that:

- each `G_i` is a non-discrete, compactly generated, locally compact group that is
  just-non-compact and has no nontrivial abelian normal subgroup;
- `Γ < G_1 × G_2` is a cocompact lattice whose projections to `G_1` and to `G_2`
  both have dense image;
- `S` embeds in `Γ`.

This is prerequisite P1 of `boone-higman-via-bader-shalom-lattice-hosts`. It does
not ask for compact presentation of the factors; that is P2,
`simple-in-bader-shalom-lattice-forces-compact-presentation`.

**Variant used if P2 fails.** P1c is P1 with both `G_i` additionally compactly
presented. By `product-lattice-fp-iff-factors-compactly-presented`, P1c alone,
together with the established imports, implies Boone–Higman.

## Attempts

1. **Which factor classes can possibly work (heretic lane c-bhdec1, 2026-09-17).**
   Let `Γ < G_1 × G_2` be as in the statement. By
   `bader-shalom-normal-subgroup-theorem`, item 2, each projection
   `p_j : Γ → G_j` is injective. Three whole classes of factors die at a precise
   step.

   - **(a) Linear factors die.**
     - *Invariant:* residual finiteness.
     - *Step where it dies:* if some `G_j` embeds as an abstract group in
       `GL_n(K)` for a field `K`, then `Γ ↪ G_j` is finitely generated (by
       `product-lattice-fp-iff-factors-compactly-presented`, item 1) and linear.
       So `Γ` is residually finite by
       `finitely-generated-linear-groups-are-residually-finite`.
     - *Conclusion:* a subgroup of a residually finite group is residually finite,
       and an infinite simple group is not. So no linear factor on either side can
       ever host an infinite simple `S`. This kills every arithmetic host
       (Margulis NST lattices, S-arithmetic lattices in products of trees or
       buildings, and every example of more than two factors listed by Caprace,
       arXiv:1709.05949, p. 36: "All those groups are linear, hence residually
       finite").
   - **(b) Two Haagerup factors die.**
     - *Invariant:* property (T) against the Haagerup property.
     - *Probe:* `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree` gives, for
       any decidable input, an infinite finitely generated simple Kazhdan group
       `H` with solvable word problem. Take `S = H`.
     - *Step where it dies:* if `G_j` has the Haagerup property, choose a proper
       continuous conditionally negative definite function `ψ` on `G_j`. Then
       `ψ ∘ p_j` is conditionally negative definite on the Kazhdan group `H`, hence
       bounded by the Delorme–Guichardet theorem. By properness `p_j(H)` is
       relatively compact, say in the compact set `K_j`.
     - *Conclusion:* if both factors are Haagerup, then `H ⊆ Γ ∩ (K_1 × K_2)`,
       which is finite because `Γ` is discrete. This contradicts `H` being
       infinite. So universality forces a non-Haagerup factor, which kills products
       of two trees and cube complexes (closed subgroups of `Aut` of a tree or a
       CAT(0) cube complex are Haagerup).
     - *Stronger form:* with one Haagerup factor `G_1`,
       `H ⊆ Γ ∩ (K_1 × G_2)`, which projects to a discrete subgroup of `G_2`.
       So the other factor contains the Kazhdan probe discretely.
     - *Trust:* Delorme–Guichardet and the standard facts on the Haagerup property
       of tree and cube-complex automorphism groups are used without verbatim
       citation. This item is recorded as an obstruction sketch, not as an
       established claim.
   - **(c) CAT(0) product factors die, conditionally.**
     - *Setting:* if both `G_i` act properly and cocompactly on proper CAT(0)
       spaces `X_i`, then `Γ` acts properly and cocompactly on `X_1 × X_2`.
     - *Step where it dies:* the Dehn function of `Γ` is quadratic, so every
       finitely generated subgroup has word problem in one fixed recursive time
       class. `complexity-bounded-host-classes-are-not-universal` kills any such
       class.
     - *Trust:* this is Idea 14 of `research/artifacts/ideas-bh-round2-2026-09-14.md`
       ("DEAD by the wall"). That bound is quoted there from BORS and marked
       *unpinned*, so (c) inherits that trust level.

   **Survivors.** Every universal family must use, on at least one side:
   - a non-linear factor (on both sides, by (a));
   - a non-Haagerup factor;
   - a factor that does not act properly cocompactly on a CAT(0) space.

   Caprace (loc. cit., p. 36) states there is "currently no known example of a
   lattice in a product of more than two non-linear locally compact groups
   satisfying the hypotheses of the Bader–Shalom Normal Subgroup Theorem 4.21".
   For two factors, the known non-linear examples are Burger–Mozes / Rattaggi /
   Wise-type lattices in products of trees, which die by (b). So P1 needs a new
   kind of lattice in a product of two non-linear, non-Haagerup, non-CAT(0)
   factors. Non-uniform lattices are not an escape inside this claim: the route
   imports only the uniform theorem. The "integrability" extension (Caprace,
   p. 28) would need its own import and its own finiteness theorem.

   **Status after this attempt:** OPEN. No candidate factor class is known to
   survive (a), (b) and (c) simultaneously, and none is known to fail.

2. **Belief breaker: one bad factor suffices, twice (swarm-0917 w17, 2026-09-19).**
   Attempt 1 intersected with the discrete `Γ`, so it needed both factors bad.
   NST item 2 (each `p_j` is injective) together with
   `fg-infinite-simple-groups-are-minimally-almost-periodic` needs only one bad
   factor. Two established obstructions follow.

   - **(b') One Haagerup factor dies**
     (`one-haagerup-factor-kills-bader-shalom-universality`).
     - *Invariant:* property (T) of the probe `H` against Haagerup.
     - *Step where it dies:* `cl p_j(H)` is compact by Delorme-Guichardet
       (`delorme-guichardet-property-t-implies-fh`, verbatim BdlHV import).
       Injectivity then maps the infinite simple `H` nontrivially into a compact
       group.
     - This settles 1(b) in its one-factor form. The survivor of 1(b)'s
       "stronger form", a Kazhdan probe sitting discretely in the other factor,
       does not exist. Amenable factors and tree factors die, and so does
       every lattice in (tree) × (anything).
   - **(c') One finite-dimensional CAT(0) factor with compact point stabilizers
     dies** (`cat0-factors-kill-bader-shalom-universality`).
     - *Probe:* `P = [F,F]`, the golden-mean group. It is simple, periodic and of
       intermediate growth, and it has solvable word problem because it lies in
       a finitely presented simple group
       (`golden-mean-periodic-group-lies-in-a-contracting-rsg`).
     - *Step where it dies:* by Izeki-Karlsson Corollary 4 (verbatim,
       `izeki-karlsson-torsion-groups-fix-cat0-points`), `p_j(P)` fixes a point
       of the factor's space. So `p_j(P)` lies in a relatively compact
       stabilizer, and injectivity gives the same contradiction.
     - This replaces 1(c). It needs no cocompactness, no Dehn function bound and
       no properness of the space, and only one side. It kills every Ã2,
       Fuchsian or Kac-Moody building factor and every finite-dimensional cube
       complex factor, including the non-Haagerup ones that (b') misses.
   - **Both at once.** Take the input `S = H_P`, the decidable simple Kazhdan
     host of `P`. Then one lattice must defeat both probes.

   **Survivors, upgraded.** If P1 holds for `S = H_P`, each factor `G_i` of the
   hosting lattice has all of the following properties:
   - non-linear;
   - not Haagerup;
   - admits no isometric action with relatively compact point stabilizers on any
     finite-dimensional complete CAT(0) space;
   - contains the non-compact closed subgroups `cl p_i(H_P)` and `cl p_i(P)`,
     and `p_i(P)` fixes a point in every action of `G_i` on such a space.

   The known non-linear two-factor examples (Burger-Mozes, Wise, Rattaggi) and
   every building-type Kac-Moody product therefore die on **each** side
   separately. A candidate would have to be a pair of non-linear tdlc groups of
   "infinite-dimensional" type, for example almost-automorphism or Neretin-like
   groups. Neretin groups themselves are Haagerup and die by (b'), at the trust
   level of `haagerup-cut-out-completions-force-haagerup-quotients-proof`.

   **Next test.** Does some non-linear, non-Haagerup, compactly generated simple
   tdlc group with no proper action on a finite-dimensional CAT(0) space even
   contain a cocompact lattice with dense projections in a product? No such
   lattice is known. Caprace (arXiv:1709.05949, p. 36) records no non-linear
   example beyond tree products.

   **Status after this attempt:** OPEN. Belief in P1 should drop. Every
   lattice class named in Attempt 1 is dead as a host of `H_P`: the linear ones
   by (a), and the tree and building products on one side alone.
