---
rg: 2
id: higman-group-satisfies-boone-higman
kind: claim
title: Higman's four-generator group embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that is the conjecture for every finitely generated group with solvable word problem; this is its test case at Higman's group, which is neither residually finite nor linear.
  baumslag-gersten-group-satisfies-boone-higman: that is the open case of the Baumslag--Gersten group; this is the open case of Higman's four-generator group.
  higman-group-embeds-in-no-almost-automorphism-group: that rules out every host inside an almost-automorphism group; this is the open embedding question itself.
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
---

**OPEN.** Let `H4 = < g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i ∈ Z/4 >`. The question is whether some finitely presented simple group contains `H4`.

**Known inputs.**
- **Word problem.** The word problem of Higman's group is decidable in polynomial time (Diekert--Laun--Ushakov, arXiv:1103.1232; abstract checked on 2026-09-13). So `H4` is a genuine Boone--Higman input.
- **No finite quotients.** `H4` has no nontrivial finite quotient (Higman 1951; recorded on main, §0 of `research/artifacts/higman-group-gottschalk-host-2026-09-12.md`).
- **BS(1,2) is forced.** Any nontrivial image of `H4` contains `BS(1,2)`. This is the hand lemma in approach 3 of `research/artifacts/ideas-2026-09-13/bh/bh-ec-groups.md`.
- **Geometry.** `H4` acts cocompactly on a CAT(0) square complex (Martin, arXiv:1506.02837; abstract-level only).
- **Not previously listed.** `H4` is not among the classes in BBMZ arXiv:2306.16356v3, Problem 5.3 (text read in the ideas artifact above).

## Attempts

- **Residually finite, linear and self-similar hosts: dead.**
  - Every finite image of `H4` is trivial, so `H4` embeds in no residually finite group.
  - Finitely generated linear groups are residually finite (Malcev), so no linear group contains `H4`.
  - A group acting faithfully on a locally finite rooted tree is residually finite: level stabilizers have finite index and intersect trivially. So no self-similar group contains `H4`.
- **Almost-automorphism hosts: dead.** By `higman-group-embeds-in-no-almost-automorphism-group`, every homomorphism from `H4` into any `A_(d,r)` is trivial. This rules out Higman--Thompson groups, Röver--Nekrashevych groups, and every finitely presented simple subgroup of them.
- **Brin--Thompson hosts `nV`, `n ≥ 2`: reduced, not decided** (2026-09-13, `higman-group-images-in-nv-force-zero-entropy-bs12-cycles`).
  - Any nontrivial homomorphism into `nV` sends every generator to an infinite-order element. Each consecutive pair generates `BS(1,2)`, and every generator has an open periodic set, a nonempty aperiodic core invariant under its conjugator, logarithmic exponent growth and zero topological entropy.
  - So `H4 ≤ nV` needs `bs12-embeds-in-brin-thompson-2v` for that `n`, with four zero-entropy witnesses in a cycle. The recorded odometer realization dies here as a source of generators: its baker-map conjugator has entropy at least `log 2`.
- **Type (A) actions of `H4` itself: constrained (hand remarks, not nodes).**
  - A point stabilizer with finitely many double cosets can fix no vertex of an unbounded Bass--Serre tree of `H4`, because double cosets of a vertex stabilizer determine the tree distance.
  - It cannot be commensurated either. Finite bi-index plus commensurated gives finite index (approach 1 of `research/artifacts/ideas-2026-09-13/bh/bh-tbt-universality.md`), and `H4` has no proper finite-index subgroup, since the core of one would give a finite quotient.
  - No candidate stabilizer was found. PBH needs a finitely presented overgroup actor anyway.
- **Piecewise-analytic circle hosts: dead** (2026-09-13,
  `higman-group-embeds-in-no-piecewise-analytic-circle-group`).
  - Every homomorphism from `H4` to a group of piecewise real-analytic circle
    homeomorphisms with finitely many pieces is trivial. This covers PL circle
    groups and piecewise-`PSL_2(R)` groups, among them Thompson's `T` and Lodha's
    finitely presented simple group `S`.
  - For PL groups and `T` this already follows from one relation, because an
    element of a PL group conjugate to its square is trivial. The full cycle is
    needed for hosts that contain `BS(1,2)`, such as Lodha's `S`
    (arXiv:1710.06220v2, Corollary 5.3).
  - It is the piecewise-analytic counterpart of Rivas--Triestino Theorem C, which
    treats `C^1` actions. By their Theorem A, `H4` does act faithfully on the line
    by homeomorphisms.
- **Finite-entropy hosts: odometer-type generators dead; entropy is 0 or infinity** (2026-09-18,
  `equicontinuous-bs-bases-force-conjugator-entropy`, lane proof, unreviewed).
  - Each generator is conjugate to its square, so its entropy `h` satisfies `h = 2h`, hence
    `h ∈ {0, ∞}` in any compact metrizable host.
  - In finite-entropy hosts (`nV`, `2V_tau`, the affine `2V_(G_N)`, every isometric-section brick
    group) all four generators have `h = 0`. By the new node, no generator can then be an
    equicontinuous map whose closure has a continuous quotient `Z/2` and fixes no point by an
    element outside `cl<γ^2>`. This kills, as generators, the `2V_tau` odometer `s`, all its
    conjugates, and all free 2-adic translations, whatever the conjugators are.
  - **Design lead, not a claim.** A host in which generators have `h = ∞` escapes every
    finite-entropy obstruction on this node at once. Such elements exist in twisted Brin--Thompson
    groups `SV_G` whenever `G` has infinite orbits on `S` (coordinate shifts of `C^S`). Also, the
    coordinate shift `σ` of `C^Z` is conjugate to `σ^2` in `Homeo(C^Z)`: pair coordinates
    `(2j, 2j+1) ↦ j` through a homeomorphism `C × C ≅ C`. Whether a conjugator can be chosen inside
    some `SV_G` is open. One heuristic obstruction, not proved: at a constant configuration (fixed
    by every coordinate permutation), the brick labels of an element of `SV_G` would force `σ` to be
    conjugate to `σ^2` modulo finitary permutations, which fails when `σ` has finitely many
    infinite orbits (the number of ends changes). This uses the per-brick description of `SV_G`
    elements, recalled from Belk--Zaremsky and not re-read at source. So an `SV_G` host for `H4`
    would need generators whose coordinate labels have infinitely many infinite orbits, or labels
    that vary between bricks.

- **Not yet tested:**
  - rational similarity groups, beyond the germ constraint `rsg-proper-power-conjugate-germs-torsion-at-finite-orbits` (at a rational periodic point of `g_(i+1)` with finite `g_i`-orbit, a power of `g_(i+1)` is the identity nearby); the equicontinuity question is `finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous`;
  - full groups of shifts of finite type with several cone types, or of non-amenable groupoids;
  - twisted Brin--Thompson envelopes over a finitely presented type (A) actor containing `H4`.

  Any host has to contain `BS(1,2)` and has to act on its Cantor space with at least one generator of `H4` not equicontinuous.

- **Proper cocompact CAT(0) hosts: dead** (2026-09-18,
  `homogeneous-conjugation-invariants-vanish-on-bs-bases`, lane proof, unreviewed).
  A conjugation-invariant homogeneous quantity is zero or infinite on any element
  conjugate to a proper power of itself. Taking the quantity to be asymptotic
  translation length gives `l(g_i) = 0` in every isometric action of every
  overgroup on every metric space, so no generator is ever loxodromic. In a proper
  cocompact isometric action on a complete CAT(0) space every element is
  semisimple and point stabilizers are finite, so an infinite-order element with
  `l = 0` cannot exist. Since every nontrivial image of `H4` contains `BS(1,2)`,
  **no group acting properly and cocompactly by isometries on a CAT(0) space
  contains `H4`.** This excludes the Burger--Mozes groups, Wise's lattices and
  every finitely presented simple group acting properly cocompactly on a CAT(0)
  cube complex. Martin's cocompact action of `H4` itself is consistent with this,
  because it is not proper: its vertex stabilizers are infinite. The same
  quantity also gives `scl(g_i) = 0` for every generator.
- **The permutational closure theorems cannot be applied through `H4`'s own
  splittings** (2026-09-18, `retracts-inherit-proper-power-conjugacy`, lane proof,
  unreviewed). A retract inherits every proper-power conjugacy of its own
  elements, so the edge group of each amalgam decomposition on main, and of the
  index-two twisted double, is a retract of neither side; and `H4` is perfect,
  hence not an HNN extension. So `pbh-class-closed-under-common-retract-amalgams`,
  `pbh-class-closed-under-graph-products` and clause (T) of
  `pbh-class-closed-under-relative-holomorphs` all fail at their hypotheses here.
  This is a method-kill and not an obstruction: `B_A` is closed under subgroups.
