---
rg: 2
id: one-relator-groups-satisfy-boone-higman
kind: claim
root: true
title: Every one-relator group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over every finitely generated group with solvable word problem; this only over one-relator groups, which have solvable word problem by Magnus, so it is a strictly weaker open problem that the conjecture implies.
  hyperbolic-groups-satisfy-boone-higman: that covers hyperbolic inputs, among them every one-relator group with torsion and every one-relator group with negative immersions; this asks for all one-relator groups, including non-hyperbolic torsion-free ones such as BS(1,2) and the Baumslag--Gersten group.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that covers groups acting on locally finite trees, including the one-relator groups BS(m,n) and the finitely generated free-by-cyclic one-relator groups; this asks for every one-relator group, most of whose Magnus--Moldavanskii splittings have associated subgroups of infinite index.
  fp-residually-finite-boone-higman: that is item (12) of the same survey list, about finitely presented residually finite inputs; this is item (9), about one-relator inputs, which need not be residually finite.
  one-relator-groups-are-coherent: that is a subgroup finiteness theorem for one-relator groups; this is an embedding problem for them, and coherence does not imply it.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**OPEN.** Every one-relator group `G = <A | r>` embeds in a finitely presented
simple group.

## Where it is asked

- **Belk--Bleak--Matucci--Zaremsky,** *Progress around the Boone--Higman
  conjecture*, arXiv:2306.16356v3, Problem 5.3: "Prove the Boone–Higman
  conjecture for: ... (9) One-relator groups (without torsion)." The survey's
  Remark 5.4 reports no progress on item (9).
- **Linton--Nyberg-Brodda,** arXiv:2501.18306, Problem 1.8.6: "Can every
  one-relator group be embedded into a finitely presented simple group?"

Only the torsion-free case is open. One-relator groups with torsion are
hyperbolic (B. B. Newman), so they are covered by
`hyperbolic-groups-satisfy-boone-higman`. Survey Theorem 5.1(9) lists them, and
Linton--Nyberg-Brodda remark that "every one-relator group with torsion embeds
into a finitely presented simple group".

It is a special case of `boone-higman-conjecture` by
`one-relator-bh-from-boone-higman`. It is a root because it is a named open
problem in its own right, and because it has a route that does not exist for
general inputs: `one-relator-bh-via-magnus-moldavanskii-hierarchy`.

## What known theorems already cover

- **Torsion:** hyperbolic, as above.
- **Negative immersions,** equivalently every two-generator subgroup is free:
  hyperbolic by Linton, *One-relator hierarchies*, Theorem 7.2, so covered by the
  same theorem.
- **Finitely generated free-by-cyclic one-relator groups** (Moldavanskii's
  criterion, often called Brown's criterion): Bux--Llosa Isenrich--Wu,
  `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman`.
- **BS(m,n):** the same source.
- **Virtually finitely generated free-by-cyclic one-relator groups,** including
  the torsion-free two-generator virtually RFRS ones:
  `virtually-free-by-cyclic-groups-satisfy-boone-higman`.

What remains is torsion-free one-relator groups with a non-free two-generator
subgroup that are neither virtually finitely generated free-by-cyclic nor
Baumslag--Solitar. The Baumslag--Gersten group
`<a,t | (t a t^-1) a (t a^-1 t^-1) = a^2>` is one: it is not residually finite,
and by `baumslag-gersten-base-is-elliptic-in-every-tree-action` it lies in no
Bux--Llosa Isenrich--Wu host over free, abelian or nilpotent vertex groups. No
theorem cited here covers it.

## Attempts

1. **Magnus--Moldavanskii induction.** `magnus-hnn-permanence-forces-one-relator-boone-higman`
   shows that the whole problem follows from the permanence premise
   `bh-embeddability-survives-magnus-subgroup-hnn`, where the base group may
   already be assumed to embed. That premise follows from
   `bh-embeddability-survives-decidable-edge-hnn` by
   `magnus-hnn-permanence-from-decidable-edge-permanence`. Both are open.
   *Deferred* to those claims.
2. **Locally finite trees (Bux--Llosa Isenrich--Wu Theorem 10.5).** This needs
   edge groups of finite index in the vertex groups. A Magnus HNN step with base
   `H` has free associated subgroups of equal rank. If both have finite index,
   then `H` is virtually free and torsion-free, hence free (Stallings--Swan).
   So the theorem reaches only steps over free bases, among them the doubly
   ascending steps (finitely generated free-by-cyclic groups) and `BS(1,n)`.
   *Dies* for steps whose base is not free, for example the Baumslag--Gersten
   step over `BS(1,2)` with cyclic edges of infinite index.
3. **Hyperbolic combination.** Linton, Theorem 7.1: a one-relator hierarchy is
   quasi-convex with hyperbolic top group exactly when it is Z-stable and the
   group contains no Baumslag--Solitar subgroup. So hyperbolicity reaches no
   group with a Baumslag--Solitar subgroup. *Dies* there.
4. **Virtual specialness outside primitivity rank two (2026-09-13).** *Adds no
   class.* Linton--Nyberg-Brodda, Theorem 2.6.16 and Corollary 2.6.17, say that
   `π(w) ≠ 2` makes every Magnus hierarchy quasi-convex, and `G` virtually compact
   special and linear. But `π(w) ≠ 2` covers only proper powers (torsion), 2-free
   relators and free groups. All of these are hyperbolic or free, so
   `hyperbolic-groups-satisfy-boone-higman` already covers them. What linearity
   still contributes is `char-zero-linear-groups-satisfy-boone-higman` for linear
   inputs with `π(w) = 2`. The residual must therefore be non-linear.
5. **A residually finite residual case (2026-09-13).**
   `drutu-sapir-group-satisfies-boone-higman`:
   - `DS = <a, b | a^2 b^2 a^-2 b^-1>` is torsion-free, residually finite and not
     linear [DS05, via Linton--Nyberg-Brodda p. 27].
   - It contains `BS(1,2)`, so it is neither hyperbolic nor virtually free-by-cyclic
     (`virtually-free-by-cyclic-groups-contain-no-bs-one-n`).
   - It is an ascending HNN extension of `F_2`, isomorphic to
     `(Z[1/2] * Z[1/2]) ⋊ Z`
     (`drutu-sapir-group-index-two-squaring-mapping-torus`).
   - So the residual is not only non-residually-finite groups such as
     Baumslag--Gersten. No imported theorem reaches `DS`; attempt 6 settles it.
6. **Power-map ascending HNN steps (2026-09-13).** *Settles `DS`, not the root.*
   `power-map-free-mapping-tori-satisfy-permutational-boone-higman` puts every
   ascending HNN extension of `F_n` along `x_i -> x_π(i)^(m_i)` in `B_A`, through
   `pbh-class-closed-under-relative-holomorphs`. This covers `DS`, by the route
   `drutu-sapir-bh-via-power-map-mapping-tori`. The root stays open. These are not
   reached:
   - Magnus steps over non-free bases, such as Baumslag--Gersten;
   - ascending steps whose endomorphism is not realized as a partial-conjugation
     mapping torus in the sense of that claim.
7. **Locally finite geometric hosts (2026-09-17).** *Dies* for every
   one-relator group containing the Baumslag--Gersten group.
   `bg-pattern-groups-act-on-no-locally-finite-cat0-complex`: whenever
   `b a b^-1 = a^2` and `t a t^-1 = b`, the element `a` acts trivially in every
   action with finite `<a>`-orbits. The exact step is Step D of
   `bg-pattern-groups-locally-finite-host-obstruction-proof`: the closure of `<a>`
   is compact in `Sym(S)`, and the smallest-prime argument kills it.
   - Conjugacy of `a` with `a^2` forces translation length 0, so `a` is elliptic
     on any locally finite tree or locally finite CAT(0) complex with finitely
     many shapes, and it then has finite orbits.
   - So Bux--Llosa Isenrich--Wu Theorems B, 10.5 and 11.1, lattices in products
     of trees, and locally finite cube complexes cannot host `BG`, whatever the
     vertex groups. This closes the question left open in
     `baumslag-gersten-base-is-elliptic-in-every-tree-action`.
   - Any host for the Baumslag--Gersten step must give `a` an infinite orbit
     on the permuted set, i.e. a non-compact cyclic closure.
8. **Assembling an envelope from the known permanence calculus (2026-09-17).**
   *Dies* for every one-relator group containing a nontrivial BG cycle, e.g. `BG`.
   See `bg-cycle-triviality-is-closed-under-the-pbh-calculus`.
   - The quasi-identities "`a_(i+1) a_i a_(i+1)^-1 = a_i^2` around a cycle closed by
     a conjugation imply `a_0 = 1`" hold in:
     - residually finite, linear, hyperbolic, proper CAT(0) and PL interval seeds;
     - free products, retract amalgams, graph products, restricted wreath products;
     - periodic extensions;
     - partial-conjugation mapping tori (T) and RF relative holomorphs.
   - `BG` violates them. The exact failing step is the HNN extension of
     `BS(1,2) ∈ 𝒫` along `<a> → <b>`, i.e. the Magnus-subgroup HNN step itself.
     So `bh-embeddability-survives-magnus-subgroup-hnn` cannot be derived from
     those operations.
   - A proof must use a seed that already carries a BG cycle (Thompson-like,
     Leavitt or highly transitive actors, whose status is open), or a
     permutation-realized HNN step along which `a` has infinite orbits.
9. **Status check and new hosts (2026-09-18).** *Constrains; the root stays open.*
   - **The hierarchy reduction is already complete.** The induction on the
     Magnus--Moldavanskii hierarchy is landed as
     `magnus-hnn-permanence-forces-one-relator-boone-higman`. Its edge
     hypotheses (free Magnus subgroups, decidable membership, computable edge
     isomorphism) are checked in `magnus-moldavanskii-hierarchy-with-decidable-edges`
     and `magnus-hnn-permanence-from-decidable-edge-permanence`. The whole gap is
     the one HNN step `bh-embeddability-survives-magnus-subgroup-hnn`, which is
     equivalent to this root on the shift data the induction uses. The
     Baumslag--Gersten step over `BS(1,2)` is its sharpest known instance.
   - **Literature.** An arXiv search for "Boone-Higman" through 2026-09 (API
     query, titles and abstracts) finds no progress on one-relator groups beyond
     Bux--Llosa Isenrich--Wu (arXiv:2408.05673). The newer entries are
     Belk--Fournier-Facio--Hyde--Zaremsky (Aut(F_n), arXiv:2503.21882),
     Fournier-Facio--Kropholler--Lyman--Zaremsky (arXiv:2506.02319),
     Fournier-Facio--Wu--Zaremsky (abstract twisted Brin--Thompson groups,
     arXiv:2603.24687) and Almeida--Dantas--Oliveira-Tosti (permutational wreath
     products, arXiv:2609.01868). None treats one-relator groups or `BG`.
   - **Odometer-extended Brin--Thompson hosts.**
     `bg-in-isometric-brick-hosts-needs-unbounded-exponents` shows
     that the `BS(1,2)` inside the finitely presented simple group `2V_τ` never
     extends to `BG`. A `BG` image in `nV`, `2V_τ` or the affine `2V` hosts needs
     a base with zero periodic exponents and unbounded exponent sums, and a
     zero-entropy conjugator. In `nV` that includes a witness for
     `bs12-embeds-in-brin-thompson-2v`.

## Update (bh-free-05, 2026-09-18)

Partial progress, lane proofs, not reviewed:
- `ascending-hnn-of-free-groups-satisfy-boone-higman`: every ascending HNN extension of a finitely generated free group is BH, and PBH.
- `almost-all-one-relator-groups-satisfy-boone-higman`: with Sapir--Špakulová, arXiv:0809.4693, (1) almost every one-relator group with at least three generators is BH, with probability tending to 1; (2) so is every one-relator group meeting their embedding criteria, or Brown's criterion for two generators.

The problem stays OPEN for arbitrary one-relator groups. For example the Baumslag--Gersten group is not residually finite, so it lies in no ascending HNN extension of a free group.

Correction (bh-free-05, same day): the "almost every one-relator group" part adds nothing new, because generic one-relator groups are hyperbolic (Gromov; Ol'shanskii) and so are covered by `hyperbolic-groups-satisfy-boone-higman`. What is new is BH for the explicit criteria (Sapir–Špakulová `thm1`/`lm4`, Brown), which include non-hyperbolic one-relator groups.
