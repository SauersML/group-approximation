---
rg: 2
id: decidable-algebras-embed-in-z2-sft-boundary-product-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds unitally in B_Ω ⊗ L_∂ for some free minimal Z^2-SFT Ω with finitely presented crossed product
distinct_from:
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that allows any torsion-free Farrell–Jones acting group and any Cantor space; this fixes the acting group Z^2 × F_d and the space Ω × ∂F_d with Ω a free minimal Z^2-SFT, and implies that claim.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one quantum rigid free minimal Z^2-SFT over some field; this asks, over F_2, for a family of them whose boundary tensors contain every decidable group algebra.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem.
Then there are:
- a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω = LC(Ω, F_2) ⋊ Z^2` finitely
  presented;
- some `d >= 2`;
- a unital embedding `F_2[G] -> B_Ω ⊗ (LC(∂F_d, F_2) ⋊ F_d)`.

**Why it matters.** Through
`cantor-crossed-hosts-are-closed-under-boundary-products`, it implies
`decidable-group-algebras-have-fp-cantor-crossed-hosts` (route
`cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`), and hence
`boone-higman-conjecture` along the graph's chain.

Unlike the bare `Z^2` case (Attempt 2 on the target), a positive answer does
not make `G` linear sofic through a rank model, because the host has none.

**Prerequisites that can fail separately** (artifact Section 4):
- (Q) Existence of one quantum rigid free minimal `Z^2`-SFT over `F_2`. This is the
  `F_2` form of `free-minimal-z2-sft-is-quantum-rigid`.
- (H) The SFTs used must have no uniform recursive language bound. That this is
  necessary is only sketched: it is the table argument of Attempt 6 on the
  target, run over `Z^2 × F_d`.
  - Without freeness and rigidity, hard minimal SFTs exist
    (`minimal-z2-sfts-have-no-uniform-language-time-bound`).
- (E) The embedding.

## Attempts

1. **Prerequisite (H) is now a theorem; the remaining gate is joint (2026-09-18, transplanter via
   entropy-measure).**
   - `z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages` (ESTABLISHED, unreviewed) proves
     the necessity of (H). The proof evaluates the host on the orbit representations
     `π_(ω,ξ)` at `δ_e`, which form a faithful family. The answer is read off one Ω-window
     `ω|_(Q_R)` and one boundary prefix `ξ|_R`, with `R = O(l)`. So an embedded `G` has its word
     problem decided in time `2^(O(l^2)) · t_Ω(O(l))`. The complexity-bounded non-universality
     principle then gives, for each recursive `T`, a two-generated decidable `H` that no
     `T`-decidable `Ω` can host.
   - Hardness together with freeness and minimality is already available
     (`minimal-free-z2-sfts-have-arbitrarily-hard-row-languages`), so hardness alone is not a gate.
   - What the target now forces is the joint statement `hard-quantum-rigid-free-minimal-z2-sfts-exist`
     (route `hard-rigid-z2-sfts-from-z2-sft-boundary-host-embeddings`). It asks for quantum rigidity
     over `F_2` and arbitrarily hard languages in the same shifts. That joint statement is a new
     prerequisite that can fail on its own. A proof that quantum rigid free minimal `Z^2`-SFTs have
     one recursive language bound would refute this target.
2. **Entropy/measure transplant: dead as a refutation.** No rank model is available: the host has
   none, by `cantor-crossed-hosts-are-closed-under-boundary-products` (3). The patterns-per-ball
   growth bound of `crossed-product-growth-bounded-by-ball-patterns` is vacuous here. `B_P(n)` in
   `P = Z^2 × F_d` grows exponentially, so the bound dominates the growth of every finitely
   generated algebra. Zero topological entropy of `Ω`, forced by
   `positive-entropy-sft-crossed-products-are-not-fp`, bounds only the `Z^2`-directions and gives
   no restriction on `F_2[G]`.
3. **Full-group reduction (not closed).** By part 3 of `crossed-product-growth-bounded-by-ball-patterns`
   (the germ lemma), a group `G` acting topologically freely by elements of the topological full
   group `[[Ω × ∂F_d ⋊ (Z^2 × F_d)]]` has `F_2[G]` embedded, non-unitally allowed, in the host.
   So (E) follows from such full-group embeddings.
   - Along a generic orbit, `G` then acts on `P` by bijections of bounded displacement, i.e. inside
     the wobbling group of `P`. The wobbling group of the exponential-growth group `P` contains
     free groups and much more, and no obstruction from that side is visible.
   - **∂-only variant: dead.** Acting only on `∂F_d`, i.e. taking `Ω` a point, gives a fixed host
     class with one recursive bound, which is killed by the same complexity diagonal.
4. **Sector/monodromy certificate: collapses.** An attempted certificate for rigidity in hierarchical
   shifts used chart monodromy around four quadrant sectors. In the four-sector example it reduces to
   a wall, the first-order obstruction of `sft-wall-rigidity-iff-idempotent-commutator-ideal`, and
   gives nothing beyond wall rigidity.
1. **Probability transplant: Kazhdan inputs through the full group (swarm-0917-w11-w11-bh-pull,
   2026-09-18).** The target stays OPEN.
   - *Question.* (E) must in particular embed `F_2[Γ]` for decidable Kazhdan `Γ` such as
     `SL_3(Z)`. Can `Γ` go into the copy of `[[P ⋉ X]]` in the unit group, with
     `P = Z^2 × F_d` and `X = Ω × ∂F_d`?
   - *Invariant.* Kazhdan expansion of finite orbits, set against Følner slabs in `Z^2`
     and tree centroids in `F_d`
     (`kazhdan-orbit-bound-in-amenable-by-free-groups`, ESTABLISHED).
   - *Killed class.* For amenable acting groups with an essentially free action and an
     invariant measure of full support, every Kazhdan subgroup of `[[P ⋉ X]]` is finite
     (`kazhdan-subgroups-of-free-amenable-full-groups-are-finite`, ESTABLISHED). So
     permutational hosting of Kazhdan inputs dies in the bare `B_Ω` factor and in every
     amenable crossed product of this kind. It is independent of Attempt 2 on the parent,
     where bare `Z^2` hosts force linear soficity. The obstruction here is at group
     level, and it holds for every amenable `P`.
   - *Residual shape for this host*
     (`dense-finite-free-orbits-force-finite-kazhdan-subgroups`, ESTABLISHED). A Kazhdan
     `K ≤ [[(Z^2 × F_d) ⋉ (Ω × ∂F_d)]]` is finite iff all its orbits through free points
     are finite. An infinite one needs an infinite, non-amenable Schreier graph that
     injects into `Z^2 × F_d` with bounded left displacement. Its tree coordinate must
     spread exponentially.
   - *Where it dies.* Step 2 of the finiteness route needs a `P`-invariant probability
     measure, to make almost every orbit finite. `F_d` has none on `∂F_d`. This is the
     same gap as in the Robertson–Steger counterexample
     `af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan` and in the open nV
     problem `kazhdan-subgroups-of-nv-act-with-finite-orbits`.
   - *Consequence for (E).* No bound on (E) follows, because (E) is an algebra embedding
     and need not send `Γ` to monomial units. What does follow: an embedding that sends
     an infinite Kazhdan subgroup into `[[·]]` needs an infinite free orbit of the kind
     just described. Deciding whether such orbits exist is the next fork.
1. **Host-geometry kill for Kazhdan inputs via tree-slab separators** (swarm-0917-w11-w11-z-break).
   - Result: ESTABLISHED `tree-times-zk-images-have-polynomial-ball-separators`. Its item 3 shows
     that no transitive Kazhdan orbit whose stabilizer meets a copy of `Z^4` or `F₂×F₂` finitely has an
     injective bounded-displacement map into `Z^2×F_d`.
   - Residual: need d2d6a0cb is split into the proved slab lemma and the OPEN
     `kazhdan-schreier-graphs-have-superquadratic-ball-separation`, via route
     `kazhdan-z2-free-injection-dies-by-ball-separation`.
   - Dead as stated: relative FW by pulled-back tree walls. The walls have `Z^2`-sized boundaries.
   - The target stays OPEN.
