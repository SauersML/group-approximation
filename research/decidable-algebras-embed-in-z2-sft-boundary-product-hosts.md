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
- **Kazhdan need d2d6a0cb: Schreier-level invariants of (T) that cannot kill it (2026-09-18,
  swarm-0917-w11-w11-z-pull; unreviewed).** Question: does an infinite Kazhdan group have an infinite
  transitive orbit with an injective bounded-left-displacement map into `Z^2 × F_d`? The sibling
  lease (w11-z-break) reduced the NO answer to the OPEN
  `kazhdan-schreier-graphs-have-superquadratic-ball-separation`. The items below record which
  consequences of (T) survive passage to a single orbit, and why each of them fails over `T × Z^2`.
  1. *Energy rigidity holds, but it is not enough.* Let `F` be a function on the orbit with
     `F∘s − F ∈ ℓ²` for every generator `s`. Then `s ↦ F∘s − F` is a 1-cocycle for the permutation
     representation on `ℓ²(orbit)`. By (T) it is a coboundary, so `F` is a constant plus an `ℓ²`
     function. However `Cay(Z^2 × F_d) = T × Z^2` has the same property, since its first `ℓ²`-Betti
     number vanishes and the group is nonamenable. So no finite-energy test function separates the
     two. Pulled-back tree walls are not commensurated here: their coboundaries lie in `p⁻¹(edge)`,
     which injects into `B_T(L) × Z^2` and may be infinite.
  2. *Weighted walls fail.* Try `F = 1_(A_e) · h(q(x)) · w(p(x))`, with `h` defined on `Z^2` and `w`
     on the tree. When `w` does not decay, the energy diverges on the infinite `Z^2`-fibres inside
     `A_e`. When `w` decays fast enough for `F`'s energy to be finite, `F` is already in `ℓ²` and the
     cocycle is trivially a coboundary.
  3. *The Koopman and measure routes are dead.*
     - If `K` preserves a probability measure on `Ω × ∂F_d`, then its orbit relation is a
       measure-preserving subrelation of an amenable relation. So `K` has a.e. finite orbits
       (Connes–Weiss), and `dense-finite-free-orbits-force-finite-kazhdan-subgroups` applies.
     - No such measure exists in general. The Koopman representation on `L²(μ⊗ν)` is tempered in the
       `F_d`-direction, so it does not almost contain the trivial representation, and (T) gives
       nothing.
  4. *Groupoid amenability is harmless.* `Z^2 × F_d` acts topologically amenably on `Ω × ∂F_d`. So
     the germ groupoid of `K`, an open subgroupoid, is amenable. Orbits through free points therefore
     have property A uniformly. Exact Kazhdan groups (`SL_3(Z)`, `SL_3(Z[1/p])` on its `p`-adic flag
     variety) have this property on free orbits as well, so it gives no contradiction.
  5. *Natural test orbits pass the separation test, heuristically only.* Take `SL_3(Z)` on primitive
     vectors, whose stabilizer is `Z^2 ⋊ SL_2(Z)`. By Lubotzky–Mozes–Raghunathan the Schreier graph is
     quasi-isometric to `H \ X` for the thick orbit.
     - In Iwasawa coordinates `(λ, u, m)`, the fibre over `(λ, m)` is the flat torus `R²/Z²m` scaled by
       `λ^(−3/2)`. This gives a flaring end, and balanced separators of `D`-balls are exponential
       in `D`.
     - `SL_3(Z[1/p]) / SL_3(Z)` is the vertex set of the `Ã₂` building. There, panel trees force
       exponential separators.
     - So neither orbit is a counterexample to the superquadratic conjecture, and neither answers the
       need positively. Neither estimate is written out.
  6. *Stuck at:* a (T)-specific statement stronger than "FW relative to finite-boundary sets". It must
     control walls whose coboundary has quadratic growth. Items 1–4 show that (T) acting on
     `ℓ²(orbit)`, invariant measures and the amenable germ groupoid do not supply it.
1. **Entropy-measure transplant: a commutative-rank bound for `F_2[Z^4]` (swarm-0917-w12-w12-z-pull, 2026-09-18). OPEN; dies at inhomogeneous units.**
   - **Test case.** `F_2[Z^4]` is decidable, so (E) needs `F_2[Z^4] ⊆ B_Ω ⊗ L_∂`.
   - **Heuristic for NO.** The host is a `Z^3`-graded algebra (lattice plus gauge)
     with algebraic core. That suggests commutative rank `<= 3`, just as the GK
     dimension of `LC(X) ⋊ Z^s` is bounded by `s` plus the complexity exponent.
   - **Established pieces** (`algebraic-core-gradings-bound-homogeneous-laurent-rank`):
     - (A) Units homogeneous for any rank `<= 3` grading with algebraic core never
       carry `F_2[Z^4]`. This covers the lattice-plus-gauge grading.
     - (A) Gauge-homogeneous units of any corner of `L_∂` never carry `F_2[Z^2]`.
     - (B) Subalgebras that are locally matrices over commutative algebras of local
       dimension `<= 3` never contain `F_2[Z^4]`.
     - So every YES construction must be inhomogeneous in every such grading and
       locally non-PI.
   - **Where it dies.** Four independent reasons:
     1. For an inhomogeneous unit, leading terms are not multiplicative, because
        the host has zero divisors in every degree.
     2. With dense periodic points, `LC(X) ⋊ Z` embeds only in an *infinite*
        product `∏ M_n(F[t^±])`. The domain-into-one-factor step fails there.
     3. The orbit band-matrix count bounds `dim A_{<=k} ~ k^2` only by
        `p(Ck)·Ck`. That bound is vacuous at complexity `p(n) >= n+1`, and
        exponential for `L_∂`.
     4. Growth, GK dimension and entropy do not see commutative rank inside `L_∂`,
        which contains free algebras.
   - **What would settle the fork.**
     - **NO:** a rank bound for commutative domains in `L(E)` itself, meaning no
       `F[x^±, y^±]` in any corner of `L_2`. This needs a genuinely inhomogeneous
       argument, for example through centralisers in `L(E)`.
       - Unchecked observation: for `h ∈ F_d` not a proper power, the centraliser
         of `h` in `L_∂` looks like `F[h^±]`. The reason is that `h`-invariant
         locally constant functions on `∂F_d` are constant (north-south dynamics).
     - **YES:** any embedding `L_2 ⊗ L_2 -> L_2`, even into a corner. It would carry
       the commuting isometries `s_0 ⊗ 1`, `1 ⊗ s_0`, which generate `F[x,y]`.
       - Brownlowe–Sørensen (arXiv:1603.03618) exclude this only for unital
         `*`-maps.
