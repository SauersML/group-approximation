---
rg: 2
id: aleph-one-eg-is-equivalent-to-relative-countable-eg
kind: claim
title: The Eilenberg--Ganea conjecture for groups of cardinality at most aleph_1 is equivalent to the relative countable statement REG_omega, and an aleph_1-sized counterexample can be taken to be an aleph_1-fold amalgam of one countable pair
distinct_from:
  relative-countable-eg-gives-eg-for-aleph-one-groups: that proves one direction (REG_omega implies EG up to aleph_1) and records that no converse was known; this supplies the converse, making the reduction two-directional.
  relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two: that is the per-pair engine (realizability of H <= G iff gd of the aleph_1-fold amalgam is 2); this is the global equivalence and the resulting form of a minimal counterexample.
  eilenberg-ganea-conjecture: that is the conjecture for all cardinalities; this concerns only cardinality at most aleph_1 and states an equivalence, not a proof.
artifacts: []
---

**ESTABLISHED** through `aleph-one-eg-is-equivalent-to-relative-countable-eg-proof`. Unreviewed. Both directions are proved.

## Statement

Recall **REG_ω**: for all countable `H ≤ G` with `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`, every 2-dimensional `K(H,1)` is a subcomplex of a 2-dimensional `K(G,1)`, inducing `H ≤ G`.

The following are equivalent.

- **(i)** REG_ω.
- **(ii)** Every group of cardinality `≤ ℵ_1` with `cd = 2` has a 2-dimensional `K(·,1)`.
- **(iii)** For every countable pair `H ≤ G` with `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`, the amalgam `Γ_{ℵ_1}(H,G) = ⁎_H {G_ξ : ξ < ω_1}` has `gd ≤ 2`.

## Minimal-counterexample biography (inverter reading)

Suppose the Eilenberg--Ganea conjecture fails for some group of size `≤ ℵ_1`. Then it fails for some `Γ = Γ_{ℵ_1}(H,G)` with `(H,G)` a countable pair such that:

1. `cd G ≤ 2`, `pd I_{G/H} ≤ 1` and `cd Γ = 2`;
2. `H` is not a vertex group of any splitting of `G` with free edge groups whose other vertex groups have `gd ≤ 2` (Lemma 2 of `continuous-free-chain-unions-have-gd-two-proof`). In particular `H` is not free;
3. no 2-dimensional `K(G,1)` has a `π_1`-injective subcomplex carrying `H`.

**If countable EG holds as well**, every countable subgroup `Γ_δ ≅ Γ_{ℵ_0}(H,G)` (for `ω ≤ δ < ω_1`) has `gd = 2`. So the counterexample is "almost of geometric dimension 2", like an `ℵ_1`-free non-free abelian group.

## The question left open, now in sharp form

"Countable EG implies EG for groups of size `ℵ_1`" is equivalent to "countable EG implies REG_ω". So the question of whether REG_ω is equivalent to countable EG is exactly the question whether `gd ≤ 2` transfers from the countable amalgam `Γ_{ℵ_0}(H,G)` to `Γ_{ℵ_1}(H,G)`. This is not decided here.

## Remarks

- **The swap question has answer yes.** Extending a 2-dimensional `K(H,1)` depends only on the pair, not on the chosen complex. This is Lemma (a)⇒(b) of the engine, an adjunction along a homotopy equivalence. But this alone does not reduce `ℵ_1` to countable EG: the relative realization is a genuine extra property of the pair.
- **Absoluteness (proof sketch, not part of the ESTABLISHED claim).** For countable objects coded by reals:
  - `cd G ≤ 2`, `pd I_{G/H} ≤ 1` and `gd ≤ 2` are `Σ^1_1`: each says a countable projective resolution or a countable aspherical 2-complex exists, with arithmetical checks, since van Kampen diagrams and `H_2` of the universal cover are arithmetical in the complex.
  - REG_ω is therefore `Π^1_2`, so by Shoenfield absoluteness it has the same truth value in `V`, in `L` and in every forcing extension.
  - By the equivalence, so does "EG for groups of size `≤ ℵ_1`". Unlike the Whitehead problem for `ℵ_1`-free abelian groups, the `ℵ_1` case of Eilenberg--Ganea cannot be settled by forcing or by `V = L`.
- **Higher cardinals (sketch).** For `κ ≥ ℵ_0`, let REG_κ be REG for pairs of size `≤ κ`. The same two proofs, with elementary submodels of size `κ` containing `κ` as a subset, give REG_κ ⇔ EG for groups of size `≤ κ^+`.

## Attempts

- **w4-048, 2026-09-17: obstruction mining on admissible pairs.** Landed `relative-eg-pair-base-meets-its-conjugates-in-free-groups`: `pd I_{G/H} ≤ 1` alone forces `H ∩ gHg^{-1}` free for all `g ∉ H` and `H_2(H) ↪ H_2(G)`. Profile items added: the base of a minimal counterexample is self-commensurating and malnormal modulo free. Dead candidate families: normal bases (Bestvina–Brady kernels in 2-dimensional RAAGs, fibres), proper finite-index bases, all non-free pairs in `BS(1,n)`, HNN vertex groups over non-free edge groups. Detection via doubles `G *_H G` or any countable tree of copies of `G` over `H` cannot succeed without refuting countable EG outright, since those groups are countable with `cd ≤ 2`.
- **w4-048, 2026-09-18: realization side.** Landed `trees-of-groups-with-realizable-edges-realize-vertices`. RP is transitive, descends to intermediate subgroups (so `RP(H,G) ⇔ RP(H,G')` for any overgroup `G'` with `RP(G,G')`), and is closed under amalgams and trees of groups with realizable edges. Peripheral 3-manifold pairs `(π_1 F, π_1 M)` realize iff they are admissible iff `∂M ≠ F`. Combined with the necessary conditions above, every candidate family in the brief is decided: each one either realizes or fails the pd hypothesis. No counterexample pair was found. Still open: the direction from `gd ⁎_H^{ω} G ≤ 2` to `gd ⁎_H^{ω_1} G ≤ 2`. Descent does not help here, because `Γ_ω` does not contain `H` as a realizable base unless RP already holds.
- **w5-048, 2026-09-18: realization criterion and the one-relator search.** Landed `two-cell-injective-maps-realize-relative-eg-pairs`. `RP(H,G)` is equivalent to each of: a combinatorial map from a 2-dimensional `K(H,1)` to a 2-dimensional `K(G,1)` that is injective on 2-cells (1-cells may fold); a `π_1`-isomorphic core of the cover `X_H` with at most one lift of each 2-cell; a cellular `G`-action on a contractible 2-complex that is free except for one vertex orbit with stabilizer `H`. `pd I_{G/H} ≤ 1` also forces `coker(H_2 H → H_2 G)` to be free abelian. In a torsion-free one-relator group `⟨S|w⟩`, every admissible base therefore has `H_2 = 0`, or `w ∈ [F,F]` and degree one onto the relator class. This kills surface subgroups of degree `≠ ±1`, and all nonzero-`H_2` bases when `w ∉ [F,F]`. Every w-disc subgroup (a labelled graph with a closed path reading `w` whose one-relator quotient injects) realizes, by Lyndon asphericity. No counterexample pair was found. Dead ends: Brady–Leary–Nucinkis-type Bredon fixed-set obstructions are vacuous here, since torsion-free single-base cone-offs have discrete fixed sets. A countable club-style detection also fails, because the fold kernel of `Γ_ω` is free. The `ω → ω_1` transfer stays open. Next: decide whether every admissible finitely generated pair in a one-relator group is carried by a w-disc, or search finite covers for 2-cell-injective cores.
- **w6-048, 2026-09-18: realization is relative efficiency.** Landed `relative-realization-is-relative-efficiency`. Setting: `G` has a finite 2-dimensional `K(G,1)` and `H` is finitely presented with gd at most 2. Then `RP(H,G)` holds iff `G ≅ <H,T|R>` with `|R| - |T| = χ(G) - χ(H)`, i.e. the relative defect `ρ(H,G)` is 0. The proof is self-contained: Schanuel's lemma plus Kaplansky positivity show that a finite 2-complex with group `G` is aspherical iff `χ = χ(G)`, and a cellular pushout lets any `K(H,1)` be used. `π_2` of every relative presentation is stably free of rank `ρ`, so admissibility (`π_2` splits off the relative 2-chains) and all stable-module invariants are blind to `ρ`. In one-relator `G`, the defect is `ρ(H,G) ≤ n(C) - 1` for any core `C` of `X_H`. The bound is sharp: index 2 in `Z^2` has `ρ = 1`. The w-disc criterion is the case `n(C) = 1` inside the one fixed complex `X`. The class statement "every admissible pair is carried by a w-disc" is therefore stronger than `REG_ω` needs, and was neither proved nor refuted. No admissible non-free, non-one-relator base was found. The finite-cover search was not run, because a core in a cover `X̂` certifies only `RP(H, π_1 X̂)`: descent does not go upward, and index 2 in `Z^2` is the counterexample. Next: for admissible finitely generated `H` in one-relator `G`, decide whether the core presentation `Y_1` (with `ρ = n(C) - 1`) can be reduced by `n(C) - 1` via extra generators. A first test case is a degree-one admissible base with `n(C) = 2`. Alternatively, find an admissible `H` with `ρ(H,G) ≥ 1`, which would refute `REG_ω` for finitely generated pairs.
- **w7-048, 2026-09-18: core relation elimination.** Landed `core-relation-elimination-bounds-relative-defect`. It works with the core presentation `Y_1 = ⟨H,S | x = φ(x)⟩`. Dropping the relation of each basis element that occurs exactly once in a successive 2-cell word (a triangular elimination chain of length `m`) still presents `G`, and gives `ρ(H,G) ≤ n(C) - 1 - m(C)` with no admissibility needed. This is obstruction-type:
  - Full elimination (`m = n - 1`) forces `H ≅ F(B'')/⟨⟨ū⟩⟩` with `φ(ū) ∼ w^{±1}`. Every such subgroup already realizes by one Tietze move.
  - For `n(C) = 2`, a single-occurrence elimination succeeds iff a decidable Magnus conjugacy test holds, and that again lands in the w-one-relator class.
  - A full chain exists only if every 2-cycle of `C`, with any `ZH`-coefficients, lies on one cell, which gives a Fox-matrix triangularity test.
  - For degree-one admissible bases, `H_1(H)` is torsion-free. This yields a two-cell normal form (`[u_0] = ap`, `[u_1] = bp`, fundamental class `b e_0 - a e_1`) in which `ab ≠ 0` is allowed.

  So the natural "drop core relations" reduction realizes nothing new. A counterexample to `REG_ω` for f.g. pairs must have admissible `H` outside the w-one-relator class, and every core must carry a 2-cycle on at least two cells. No such pair was found and no `ρ ≥ 1` admissible pair was produced. Next: for `n(C) = 2` with no single-occurrence basis element, decide whether `⟨S, y | λ(u_0), λ(u_1)⟩ → G` is an isomorphism (non-triangular elimination), or build an admissible degree-one base with `ab ≠ 0` and test it.
- **w8-048, 2026-09-18: two-cell core deletions need a unit Fox coefficient.** Landed `two-cell-core-deletions-need-a-unit-fox-coefficient`, which answers the `n(C) = 2` open test of `core-relation-elimination-bounds-relative-defect`.
  - `π_2` of the core relative presentation `⟨B, S | u_0, u_1, x = φ(x)⟩` is `ZG` on one explicit identity. Its cylinder coefficients are `c_x = ε g ∂_x u_0 - ∂_x u_1`, with `g = t_1 t_0^{-1} ∉ H`.
  - Admissibility is exactly unimodularity of the row `c` over `ZG`.
  - Deleting one cylinder `y = φ(y)`, in any free basis and for any `y`, presents `G` iff `c_y` is a unit and the kernel `N_y` is trivial. Also, `c_y` is a unit iff `N_y` is perfect.
  - The coset splitting `ZG = Z[gH] ⊕ Z[H] ⊕ …` together with trivial units (local indicability plus Higman) shows that `c_y` is a unit only when one Fox coefficient is `0` and the other is `±h`. That forces `ab = 0`.
  - So for `ab ≠ 0` the map `⟨S, y | λ(u_0), λ(u_1)⟩ → G` is **never** an isomorphism, including in no-singleton cases. The ab = 0 regime reduces to a ZH-Fox-singleton test plus a perfect-kernel test.
  - Handle slides act on `c` by elementary column operations. RP via extra-generator elimination for `ab ≠ 0` is therefore an elementary-completion question for the unimodular row `c` over `ZG`, and it stays open.
  - Construction side, as a negative computation: exhaustive, surface-guided and 20000 random two-w-cycle foldings (`experiments/two-cell-core-ratio-2026-09-17`) found dependent w-cycle classes only with `[u_1] = ±[u_0]` (never degree one, and not admissible by the row test) or with one class zero. No `(a,b) = (1,2)` core was found.

  Next: prove that a degree-one admissible two-cell core has `ab = 0`, which would make the w-one-relator/Fox-singleton regime the whole two-cell story. Otherwise, find an `ab ≠ 0` core and test whether its `c` is elementarily completable over `ZG`.
- **w9-048, 2026-09-18: ab != 0 two-cell cores exist, and admissibility constrains g.** Landed `degree-one-two-cell-cores-with-ab-nonzero-exist` and `two-cell-ab-nonzero-admissible-needs-g-in-conj-closure`.
  - Ratio pairs of w-loops (`z_1 = λ z_0`) are exactly the classes `h ∈ H_1(Δ)` of a fiber-product component with `p_{2*} h = λ p_{1*} h ≠ 0`. This is linear algebra, and it builds such cores directly.
  - Explicit core: `w = x y^4 x^{-1} y^{-1} x y^2 x^{-1} y^{-5}` on a 3-vertex graph, with `(a,b) = (1,2)` and `ε = 1`. It is a genuine core: `H` lies in an index-3 `K` whose cover is `C` plus one edge and one cell, and the Brodskii–Howie Freiheitssatz plus Britton give injectivity. So the step "ab = 0 for degree-one two-cell cores" cannot follow from graph or homology data.
  - The example is **not** admissible, since the character `x ↦ 2`, `y ↦ -1` kills `c`. Elementary completability of its row is therefore moot.
  - Obstruction for the admissible case: let `P = ⟨g^k H g^{-k}⟩`. Pushing `Σ c_x d_x = 1` to `Z[P\G]`, where `⟨g⟩` acts freely modulo `P`, makes `εa ḡ - b` a unit of `Z[⟨g⟩/⟨g⟩∩P]`. Since `ab ≠ 0` and `εa - b = ±1`, this forces `g ∈ P`. So `g ∈ ⟨⟨H⟩⟩`, `g ∉ N_G(H)`, and no character or representation may kill `c`.
  - Census: all 132 fiber-product configurations on 3 vertices (`λ ∈ {2, 3/2}`, `ε = 1`) are non-admissible through an `F_3`-character. The vanishing locus tracks the Alexander polynomial of `w` under `s ↦ -s`.

  Next: prove that for every `ab ≠ 0` two-cell core some character `χ` has `c^χ = 0`, for instance via the Alexander polynomial under `s ↦ -s`. That would settle `ab = 0` for admissible bases. Otherwise, find an `ab ≠ 0` configuration that passes every character test and has `g ∈ P`.
