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
refuted_by: [cantor-crossed-hosts-of-finite-cd-have-bounded-polynomial-rank]
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
**Reframing of (E): the boundary factor is only a binary Leavitt factor (swarm-0917, lane w13-bh-pull).**
- `boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts` is ESTABLISHED. For every unital `B` and every `d >= 2`,
  `F_2[G]` embeds unitally in `B ⊗ L_∂(d)` if and only if it embeds unitally in `B ⊗ L_(F_2)(1,2)`.
  - One direction is Brownlowe–Sørensen.
  - The other uses a binary Leavitt family in the corner `e = Σ_(i<d) s_i t_i`, then the augmentation extension.
- So (E) is equivalent to: every decidable `F_2[G]` embeds unitally in `B_Ω ⊗ L_(F_2)(1,2)` for some admissible `Ω`.
  The choice of `d` and the free-group boundary contribute nothing beyond `L(1,2)`.
- This is the container of reduction R2 in the artifact. The boundary factor buys finite presentation of the host
  through Theorem P. It does not buy extra embedding room.

**Consequence for the `Z^4` test case.** A NO for `F_2[Z^4]` would refute (E).
- By corollary (C2) of that claim, the sufficient condition "a corner of `L_∂` contains a Laurent ring in two
  commuting variables" is equivalent to the negation of `leavitt-commuting-units-are-algebraically-dependent`.
  That claim is OPEN, and exact centralizer computations support it.
- So any embedding of `F_2[Z^4]` must use one of three mechanisms, each of which can fail separately:
  - (i) the Leavitt corner. This is equivalent to refuting `leavitt-commuting-units-are-algebraically-dependent`.
    Because of the firewall on that claim, doing so would not decide Ara–Cortiñas Q5.7.
  - (ii) `F_2[Z^3]` in `B_Ω`, or in a corner of it. This is a rank-3 question for crossed products of `Z^2`-SFTs.
    It is the `s = 2` case of the commutative-rank heuristic, under which a `Z^s`-graded Steinberg algebra with an
    AF kernel has no commutative domain of transcendence degree `s + 1`.
  - (iii) an entangled embedding that uses neither tensor factor separately.
- Monomial embeddings are already excluded (the z4 no-monomial-embedding node on the fork branch, not yet in this
  tree).

- A parallel lane (w12-z-pull, the homogeneous Laurent-rank bound for algebraic-core gradings, not in this tree)
  kills two subcases:
  - gauge-homogeneous units in (i);
  - `Z^3`-lattice, gauge-homogeneous and locally PI units in (ii).

  So what survives is inhomogeneous, locally non-PI units.

**Where it stops.** Nothing here constructs or rules out an embedding, so the claim stays OPEN. The next test is
(ii): does any free minimal `Z^2`-SFT crossed product over `F_2` contain `F_2[Z^3]`?

**Frobenius–Cartier model kill (swarm-0917-w14-w14-z-pull, obstruction-miner / linear-characteristic, 2026-09-19).**
This attempt targets the YES side of fork (i), `F_2[Z^2] ⊂ L_∂ ≅ L_{F_2}(1,2)`.

- **The model.** Take a char-2 field `K` with p-basis `t`, e.g. `F_2(t)`. Put
  `S_i f = t^i f^2` and let `S_i^*` be the Cartier coordinates. This is a faithful
  unital model of `L_{F_2}(1,2)`, or of `L(1,2^d)` for a p-basis of size `d`.
  - Commuting multiplication operators by `K` are the obvious source of Laurent
    rings.
  - Multiplication by `t` satisfies only the infinite recursion
    `m_t = S_1 S_0^* + S_0 m_t S_1^*`.
- **Result.** `cartier-model-semilinear-leavitt-elements-are-gauge-homogeneous`
  (ESTABLISHED, unreviewed) proves:
  - a Frobenius-semilinear operator of twist `k` lies in `π(L)` exactly when it
    comes from the gauge component `L_k`;
  - the only multiplication operators in `π(L)` are `0` and `1`.
- **Consequence.** Together with `algebraic-core-gradings-bound-homogeneous-laurent-rank` (A),
  this kills every semilinear construction:
  - multiplication operators;
  - twisted Frobenius or Cartier maps;
  - `K^{2^N}`-linear (Hasse-type) operators.

  Every member dies at the Artin-independence step, which forces gauge homogeneity.
- **Where it stops.** A YES witness must mix at least two Frobenius twists in
  every such model. Non-homogeneous units remain untouched, and the claim stays
  OPEN.
**Attempt (faithful point column transplant, swarm-0917-w14; OPEN).** This transplants the
probability/random-walk habit of reading an operator through one random starting point to the regular
representation of the host. The result is `steinberg-ore-domains-have-faithful-point-columns`, ESTABLISHED
(unreviewed) with a self-contained route.

- **Lemma.** A nonzero left Ore domain `C` inside `LC(X, k) ⋊ P`, or inside any ample groupoid algebra with
  compact unit space, acts faithfully on the column of one point `x`. That is, `c |-> π_x(c) δ_e` is
  injective.
- **Proof idea.** The points killed by a nonzero `c` form a clopen set. Compactness plus the Ore condition
  produce one nonzero `h` killing every column. The columns separate elements, so `h = 0`.
- **Where it applies.**
  - `dim V_n <= |B_P(mn)|` for Ore inputs, with no pattern count factor.
  - So `B_Ω` alone, and every crossed product over a virtually nilpotent group of growth degree `D`, contains
    no `F_2[Z^(D+1)]`, whatever the space. This includes exponential-complexity free minimal SFTs.
  - The boundary factor is therefore needed for the input `Z^3` for every choice of `Ω`, not only for slow
    `Ω`.
- **Where it dies on (E).**
  - Here `P = Z^2 × F_d`, and the orbit balls `B_P(mn)` grow exponentially. The count is vacuous at every
    Ore input.
  - What survives is the structural fact: any unital `F_2[Z^4] ⊆ B_Ω ⊗ L_∂` acts faithfully on a single
    column `k^(Z^2 × F_d)` at some point `(ω, ξ)`, with the degree-`n` part supported on
    `B_(Z^2)(mn) × B_(F_d)(mn)`.
  - Turning this into a NO for `Z^4` requires a linear analog of the monomial tree-slab argument on that
    column. Such an analog would also have to exclude `F_2[Z^2] ⊆ L(1,2)`, and so decide the direction
    of `leavitt-commuting-units-are-algebraically-dependent`. The reason:
    - `F_2[Z^2] ⊆ B_Ω` through the `v_p`, and tensor products of injective maps over a field are
      injective.
    - So `F_2[Z^2] ⊆ L(1,2)` would give `F_2[Z^4] ⊆ B_Ω ⊗ L(1,2)`.
    - By the swarm's binary-Leavitt reduction, that is the same as an embedding in `B_Ω ⊗ L_∂`. That exclusion is the `F_2` shadow of Ara–Cortiñas Question 5.7
    (arXiv:1108.0352v3, p. 8), which is open.
  - So the attempt stops at that firewall.
- **Status.** (E) stays OPEN.

1. **Spectral-curve (Burchnall–Chaundy) kill of spectrally complete embeddings (swarm-0917-w14-w14-z-pull,
   obstruction-miner via linear-characteristic, 2026-09-19). Partial kill; the claim stays OPEN.**
   - **Established** (`spectrally-complete-tuples-bound-commutative-rank`, unreviewed):
     - Use any faithful row-finite representation, such as orbit representations of `B_Ω ⊗ L_∂`.
     - If commuting `L_1, …, L_s` have joint eigenspaces `W_μ` of constant finite dimension, varying rationally,
       and locally complete, then every `P` commuting with them satisfies `Φ(L, P) = 0`. Here
       `Φ = D(μ) det(y − P|W_μ)`, obtained by Cayley–Hamilton on each `W_μ` plus a Vandermonde vanishing lemma.
     - So no commutative subalgebra containing such a tuple contains `F[Z^{s+1}]`.
   - **Instances.**
     - In `LC(X, K) ⋊ Z`, every *nondegenerate* band element qualifies: those whose extreme coefficients beyond
       offset 0 are units, `≡ 1` over `F_2`.
     - In `LC(Ω, K) ⋊ Z^s`, every commuting `s`-tuple of directional nondegenerate elements along independent
       directions qualifies.
     - So an `F_2[Z^3] ⊆ B_Ω` (mechanism (ii)) contains no commuting directional nondegenerate pair.
     - An `F_2[Z^2] ⊆ LC(X, F_2) ⋊ Z` contains no nondegenerate element at all.
   - **Invariant:** the spectral curve `Φ` of `P` over the eigen-parameters of a spectrally complete tuple.
   - **Where every member dies:** the Cayley–Hamilton step, which needs `dim W_μ < ∞` together with local
     completeness.
   - **Residual gate:** degenerate elements, where an extreme coefficient vanishes somewhere and `W_μ` is `0` or
     infinite-dimensional.
     - The residual for `s = 1` is recorded as `minimal-cantor-z-crossed-products-contain-no-f2-z2`. That is
       the `s = 1` case of the commutative-rank conjecture.
     - A YES there refutes that conjecture.
     - Within its reach this is the inhomogeneous, non-graded argument that item "Entropy-measure transplant"
       asked for. It does not reach `L(1,2)` corners, because no spectrally complete tuple is known there.

**Mechanism (i): an exact commutant scout in `L_(F_2)(1,2)` (swarm-0917, lane w15-bh-pull; the claim stays OPEN).**
- **Isometries are dead as generators (proved).**
  - `leavitt-isometry-centralizers-are-monogenic` (ESTABLISHED, unreviewed) holds over any field and for any
    `L(1,n)`: `C_L(s_w) = k[s_u]` and `C_L(t_w) = k[t_u]`, where `u` is the primitive root of `w`.
  - So in a (i)-embedding, and in any `L_2 ⊗ L_2 -> L_2` map (the YES case above), neither commuting generator
    can be a monomial isometry or co-isometry, even after conjugating by a unit. In particular the images of
    `s_0 ⊗ 1` and `1 ⊗ s_0` must be non-monomial isometries.
- **Census of small elements (evidence).** `experiments/leavitt-commutant-scout-2026-09-17/`
  (`l2.py`, `commutant.py`, `scan_exhaustive.py`, `census_V12_output.txt`) has exact `F_2` arithmetic on
  depth-`N` tables.
  - It covers every `A` in the box `V_(1,2)` (depth 1, outputs of length at most 2; `2^14` elements).
  - It computes the exact commutant of `A` in `V_(2,4)` and tests the joint growth of `{A^i B^j}`.
  - Results: 15256 of the 16216 transcendental `A` have box commutant `F[A] ∩ box`. The other 960 all have
    linear joint growth, at most 22 at `k = 7` against 28 for an independent pair.
  - The larger commutants come from a matrix mechanism. They are finite modules over `F[x]` or `M_2(F[x])`, for
    example with `x` = "insert `1` after the first letter", and they are always algebraically dependent.
  - A random scan of `V_(1,3)` (`scan_random.py`) gave the same picture.
- **What this changes.** Small, shallow elements give no independent commuting pair, so a counterexample to
  `leavitt-commuting-units-are-algebraically-dependent`, if one exists, is not found by short search. This
  matches the Ara–Cortiñas firewall: an embedding `L_2 ⊗ L_2 -> L_2` would need deep, non-monomial isometries.
- **Mechanism (iii): counting dies on IBN.** Rank and dimension counts over `L` cannot separate entangled
  embeddings, because `L ≅ L^2` as modules, so `L` has no IBN, and every column count collapses.
  - What survives, by an argument sketched in the lane and not written up, is the faithful `L`-valued
    point-column lemma for minimal `Ω`: one orbit point suffices, by Ore localization plus compactness.
  - So a single `L`-valued column detects an entangled embedding. It gives no rank bound.
- **Where it stops.** Everything left in (i) is Ara–Cortiñas-hard. No embedding and no obstruction beyond
  isometries is known.

**Central-Laurent descent: the lattice-and-factor part of the `Z^4` fork is one function-field Leavitt question (swarm-0917-w15-w15-z-pull, linear-characteristic, 2026-09-19). OPEN; a new decomposition, not a decision.**
- New ESTABLISHED (unreviewed) claim `laurent-tensors-reduce-leavitt-rank-to-function-fields`, with a route that
  requires nothing.
  - **Lemma.** Let `A` be any algebra and `R` a central commutative domain with `trdeg_F Frac(R) = s`. If `A ⊗ R`
    contains a commutative domain of transcendence degree `s + m`, then `A ⊗ Frac(R)` contains `m` commuting
    elements that are independent over `Frac(R)`. At the polynomial level the converse holds.
  - **Proof idea.** Take a prime of the commutative hull of `D` and `R` that avoids both. Nonzero elements of `R`
    are non-zero-divisors in `A ⊗ R`.
- **Consequence for the host `B_Ω ⊗ L_(F_2)(1,2)`.** Let `H_Y = (LC(Y) ⋊ Z^2) ⊗ L_2`, for `Y` a point, a finite
  orbit or an odometer factor of `Ω`. The algebra `LC(Z^2/Λ) ⋊ Z^2` is `M_N(F[Λ])`, so `H_Y` is locally
  `M_N(L_2) ⊗ F[Z^2]`. Hence:
  - any `F_2[Z^4]` in `H_Y` gives `Q_2(F_2(x,y))`, that is, two commuting independent elements of
    `L_(F_2(x,y))(1,2)`;
  - `H_Y` contains mechanism (i).
- **Field reduction.**
  - `Q_2(F)` implies `Q_2(K)` for every field `K ⊇ F`.
  - `Q_2` over any field of characteristic `p` descends to `Q_2(F_p(x_1..x_e))`.
  - So the polynomial-level commutative-rank conjecture for every `L_2 ⊗ F[Z^s]` is exactly the base case over
    function fields.
- **The NO side of the fork now needs three pieces, each of which can fail:**
  1. no `F_2[Z^3]` in `B_Ω`, which is the Ore point-column lemma of lane w14-bh;
  2. no `Q_2(F_2(x,y))`;
  3. no embedding that essentially uses the expansive part of `Ω`, which is mechanism (iii-b).
- **Where it dies as a proof of NO.** At piece 2.
  - The Ara–Cortiñas Q5.7 firewall moves to `K = F_2(x,y)`: a unital map `L_K ⊗ L_K -> L_K` gives `Q_2(K)`.
  - A rank argument cannot supply piece 2, because `[1] = 0` in `K_0(L_K)`.
  - Piece 3 cannot be reached by the lemma, because the lattice units are not central in `B_Ω`.
- **Transfer.** Every *field-uniform* obstruction for `L_k(1,2)`, such as `C(s_w) = k[s_u]` from lane w15-bh,
  now covers all of `H_Y` at once.

**w16-bh obstruction-miner (linear-characteristic): the Q_2 firewall split into a skew-field half and a grading half.**
OPEN.
- **New target node.** `leavitt-algebras-contain-no-two-variable-polynomial-ring` is the field-uniform statement
  the w15 need asked for: no two commuting independent elements in `L_k(1,2)`, for any field `k`.
  - At `k = F_2` it gives `leavitt-commuting-units-are-algebraically-dependent`
    (route `commuting-units-dependence-from-field-uniform-leavitt-rank`).
  - At `k = F_2(x,y)` it kills mechanism (i), and through `laurent-tensors-reduce-leavitt-rank-to-function-fields`
    all of `H_Y`.
- **ESTABLISHED (unreviewed).** `leavitt-nonnegative-part-is-matrix-union-over-free-algebra`:
  - `L_(>=0)` is the union of the unital blocks `E_N ≅ M_(2^N)(k<x_0,x_1>)`, with connecting map
    `ψ(p)_(y,x) = ∂_y(p x_x)`.
  - A commutative domain in `M_n(D)`, where `D` is the free skew field, restricts to the image of a minimal-rank
    element. There it becomes a subfield of `M_r(D)`.
  - `r = 1` is excluded by Cohn 1978 with Schofield 1985, Thm 11.6, quoted verbatim from Derksen–Volčič,
    arXiv:2512.03223, §5.2.
  - Hence every commuting independent pair in `L_(>=0) ∪ L_(<=0)` needs a transcendence-degree-2 subfield in
    some `M_r(D)` with `r >= 2`.
  - Script: `experiments/leavitt-nonnegative-part-2026-09-19/check_matrix_union.py`.
- **Decomposition.** Route `leavitt-rank-one-from-free-field-matrices-and-degree-reduction` has two new OPEN
  prerequisites.
  - `matrices-over-free-fields-have-no-trdeg-two-subfields`: pure skew-field theory, field-uniform, known at
    `r = 1`.
  - `leavitt-polynomial-pairs-move-to-the-nonnegative-part`: the grading half.
  - Each can fail without the other.
- **Where it dies.**
  - The case `r >= 2` of the skew-field half is not in the literature I checked. Companion matrices over one
    centralizer give only transcendence degree 1.
  - The grading half cannot go through any homomorphism: `L_(>=0)` is stably finite and `L` is purely infinite.
    Leading forms fail, since `L` is not a graded domain, and conjugations preserve degree.
- **Literature check.** Bilich–Hazrat–Nam, arXiv:2512.09241, has an obstruction for the Weyl algebra in
  characteristic 0 via `C*`-completions. It says nothing about `k[x,y]` in `L_k(1,2)`. `C*` methods cannot, since
  `C(T^2) ⊆ O_2`.

**w16-z obstruction-miner (linear-characteristic), 2026-09-19: mechanism (ii) is closed down to rank 1, and the relative-commutant YES scout is already covered.**
- **Closed.** `minimal-cantor-z-crossed-products-contain-no-f2-z2` is now ESTABLISHED by the new route
  `minimal-cantor-z-no-f2-z2-via-point-column`, which is Part 5 of
  `steinberg-ore-domains-have-faithful-point-columns` with `P = Z` and `D = 1`.
  - It gives no `k[Z^2]` in `LC(X, k) ⋊ Z` for any compact `X`, field `k` or homeomorphism. Degenerate
    embeddings do not survive.
  - So the `s = 1` case of the commutative-rank conjecture holds for every `Z`-transformation groupoid.
  - With the `D = 2` case (no `F_2[Z^3] ⊆ B_Ω`), mechanism (ii) is dead at every rank.
- **Where it stops.** The point-column count gives nothing on groupoids with exponential orbit growth:
  the Cuntz groupoid and `Z^2 × F_d`. So the whole Z^4 question now sits on mechanism (i) (Q_2) and
  mechanism (iii) (entangled).
  - The NO side of Q_2 is firewalled by Ara–Cortiñas Question 5.7.
  - A YES scout on the twisted fixed-point equation `x u = u φ(x)` would repeat the screens already on
    `leavitt-endomorphism-relative-commutants-are-finite`: 843 words and 32 core units, all with
    `dim <= 2`. So it was not rerun.
  - A YES witness must use a unit with components of both signs, which
    `leavitt-triangular-endomorphism-commutants-are-finite` does not cover. Random short words do not
    reach such units, so the witness has to be designed.

**w17-z obstruction-miner (linear-characteristic), 2026-09-19: the field bound for mechanism (i) is pushed from invertible elements to universal localizations.**
- **Established.** `leavitt-polynomial-pairs-contain-a-universally-singular-element`, by
  `leavitt-polynomial-pairs-singular-element-proof` (unreviewed). A witness `k[a, b] ⊆ L_k(1,2)`, for any field `k`
  (in particular `F_2` and `F_2(x, y)`), must contain one `p(a, b) ≠ 0` with `L_(p(a,b)) = 0`. Equivalently,
  `p(a, b)` is non-bijective on every nonzero `L`-module.
  - Lemma: `universal-localizations-of-quasi-free-algebras-are-quasi-free`. Base change of the length-one bimodule
    resolution, using Bergman–Dicks `B ⊗_A B = B` and `Tor_1^A(B, B) = 0`, imported verbatim from
    Neeman–Ranicki Lemma 8.6.
  - Then `L_Σ` (`Σ = k[a, b] ∖ 0`) would be quasi-free, contain `k(a, b)` by simplicity, and contradict
    `quasi-free-algebras-have-no-trdeg-two-subfields`. Compactness and commutativity give a single element.
  - This is strictly stronger than `leavitt-algebras-have-no-trdeg-two-subfields`. `1 + s_0` (`char ≠ 2`) and
    `1 + s_0 + s_0^2` (`char ≠ 3`) are non-units that are bijective on the function module `F({0,1}^N, k)`.
  - The w16 remark that the homological method "stops at zero divisors" is therefore too pessimistic. It reaches
    every element invertible in some nonzero overring.
- **Where it dies.** The universally singular elements include isometries, zero divisors and idempotents. So
  `k[s_0]` already contains one, and the centralizer of an idempotent `e` is `eLe × (1-e)L(1-e) ≅ L × L`.
  - So no statement of the form "centralizers of singular elements have rank one" is weaker than Q_2 itself. It
    is not recorded as a prerequisite.
  - The remaining NO obstruction must say which singular element can sit in a trdeg-2 domain. Grading, leading
    forms and Hochschild dimension give no handle on that.

**w17-z-pull obstruction-miner (linear-characteristic), 2026-09-19: mechanism (i) is dead for every field; the firewall Q_2 is answered NO, and with it Ara–Cortiñas Question 5.7 over F_2.**
- **New theorem.** `quasi-free-algebras-contain-no-two-variable-polynomial-ring` is ESTABLISHED (unreviewed) by
  `polynomial-subring-bound-via-fraction-field-koszul-ext`. If `k[a_1, ..., a_n] ⊆ A'`, then
  `l.gl.dim(A' ⊗ k(y_1, ..., y_n)) >= n`, with no flatness of `A'` over the subring.
  - The trick is to resolve `Q = (A' ⊗ K) ⊗_S S/I` with `S/I ≅ Frac(C)`. The induced Koszul complex stays exact
    because `Tor^S(A' ⊗ K, S/I) = Tor^C(A', Frac C) = 0`. The top Ext is `Frac(C) ⊗_C A' ≠ 0`.
  - This answers live need `03f81334`. The subfield route (`quasi-free-subfield-bound-via-koszul-ext`) stopped
    exactly because it put flatness on the `A'` side.
- **Cascade** (compiled by `cairn check`, through existing routes):
  - `leavitt-algebras-contain-no-two-variable-polynomial-ring` holds for every field, by the new route
    `leavitt-plane-freeness-from-quasi-free-polynomial-bound`;
  - then `leavitt-commuting-units-are-algebraically-dependent` and
    `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`, which is Question 5.7 at `k = F_2`;
  - and `leavitt-unit-group-has-no-integer-heisenberg-subgroup` and
    `kun-thom-wreath-does-not-embed-in-leavitt-unit-group`.
- **For this claim.**
  - At `k = F_2(x, y)` it kills mechanism (i) of the `F_2[Z^4]` test case.
  - With `laurent-tensors-reduce-leavitt-rank-to-function-fields`, it kills every `Z^4` embedding supported on
    the equicontinuous-factor part of `B_Ω ⊗ L_2`.
  - With w16-z's closure of mechanism (ii), the `Z^4` fork now rests only on mechanism (iii), the entangled
    embeddings.
- **Where it stops.** `B_Ω ⊗ L_2` is not quasi-free, because `B_Ω ⊇ F_2[Z^2]`. The same Koszul argument only gives
  `l.gl.dim` lower bounds there, and the upper bound `leavitt-tensor-global-dimension-bound` is
  `gl.dim B_Ω + 1`. `F_2[Z^4]` contains a polynomial ring in 4 variables. So the method refutes the entangled case as
  soon as `l.gl.dim(B_Ω ⊗ K) <= 2` for `K = F_2(y_1, ..., y_4)`.
  - Whether that holds is unclear. `LC(Ω, F_2)` is a countable union of separable algebras, which can have
    Hochschild dimension `1` rather than `0`, so the naive bound for `B_Ω` is `3`, one too many.
  - Sharpest next target: bound `l.gl.dim(B_Ω ⊗ K)` by `2`, or find a module of projective dimension `3`.
**w18 obstruction-miner (linear-characteristic), 2026-09-19: a one-isometry linear criterion for mechanism (i), and a Toeplitz rung between Q5.7 and Q_2.**
- **Established.** `toeplitz-commutant-compression-detects-polynomial-pairs`, by
  `toeplitz-commutant-compression-detects-polynomial-pairs-proof` (unreviewed, elementary, any field `k`, any
  unital `k`-algebra `A`). Let `S'S = 1`, `P = 1 - SS'` and `Φ(a) = S a S'`.
  - `C(S,S') = { T : T - Φ(T) ∈ PAP }`, and `κ(T) = PTP` is a unital homomorphism `C(S,S') -> PAP` with image
    `PAP ∩ (1 - Φ)(A)`.
  - If `κ(T)` is transcendental, then `S` and `T` are commuting and algebraically independent. Proof: take the
    lowest `S`-degree, multiply by `S'^(i_0)` and then by `P`; since `PS = 0`, this leaves `p_(i_0)(κ(T)) = 0`.
  - Doubly commuting isometries with `(1 - SS')(1 - RR') ≠ 0` are exactly unital embeddings of `J ⊗ J`, where
    `J = k⟨x, y | yx = 1⟩`. Every nonzero ideal of `J ⊗ J` contains `p ⊗ p`.
  - The chain is `Q5.7 YES => J ⊗ J embeds in L => (transcendental κ for some S) => Q_2 fails at k`. A
    transcendental element of any `C_u` also gives the third condition, with `S = u s_0`.
- **Posed (OPEN).** `toeplitz-tensor-square-embeds-in-binary-leavitt`, at `F_2`. A NO answers Q5.7 negatively over
  `F_2`, and it follows from Q_2. A YES refutes Q_2 at `F_2`, the no-polynomial-pair form of mechanism (i).
- **Killed.** Every monomial, or conjugate-to-monomial, first isometry `S = s_w`.
  - `C(S,S') ⊆ F_2[s_v]` by `leavitt-isometry-centralizers-are-monogenic`.
  - `κ(s_v)` is nilpotent, since `κ(s_v)^m = P s_w P = 0`, so the compressed commutant is algebraic.
  - The invariant is the compressed commutant `κ(C(S,S'))`. It dies at the step where `κ` must be transcendental.
- **Screen.** Take `S = u s_0` for eight transvection and permutation units, in the boxes `(2,3)` and `(3,4)`. Each
  gives `C(S,S') = F_2`, while the flip control gives `M_2(F_2)`
  (`experiments/leavitt-toeplitz-commutant-2026-09-17/results.txt`).
- **Where it stops.**
  - For `F_2[Z^4]` the pair is polynomial, not Laurent, since `R` is a proper isometry and not a unit. So a YES
    here does not yet give units for the test case.
  - No non-monomial `S` with a nonscalar `C(S,S')` beyond the `M_2` controls is known.
**w20-z obstruction-miner (linear-characteristic), 2026-09-20: referee PASS on the w18 refutation. (E) is false.**
- **Result.** The chain in commit `20e819b457` is refereed and passes: `f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts`,
  via `polynomial-subrings-bound-transcendental-flat-dimension` and `cantor-crossed-products-bound-commuting-rank-by-cd`.
  That commit is on `claude/scale-agents-high-impact-erol9w` and is not on `main`. The full report is
  `crossed-product-commuting-rank-refutation-review`.
  - The invariant is universal weak dimension, `uwd(A) = sup_K w.gl.dim(A ⊗ K)`.
  - Commuting rank is at most `uwd`, and `uwd(B_Ω ⊗ L_∂) <= cd(Z^2 × F_d) = 3`. So `F_2[Z^4]` embeds in no matrix
    ring over the host, unital or not, for every `Z^2`-Cantor system Ω.
- **Where every member of the class dies.** An approach that bounds rank by a dimension of the host alone dies on
  `k(x) ⊗ k(y)`. That ring is hereditary and has commuting rank 2.
  - The w17 localization attempt died at universally singular elements, because it inverted `Σ` inside an overring
    of `A`.
  - The w18 step inverts `Σ` only in the coefficient field, through the graph `a_i ↦ y_i`. That is the step that
    passes.
- **Maintainer action on landing.** Add `refuted_by: [f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts]`
  to this node's frontmatter. That id is absent from this worktree's base, so it was not added here.
- **Side consequence (needs a second referee).** Ara–Cortiñas Q5.7 has a negative answer over every field. The
  proof uses `gl.dim L_K(1,2) = 1` (arXiv:1605.03841) and `k[s, t] ⊆ L_2 ⊗ L_2`.
**w21-z obstruction-miner (linear-characteristic), 2026-09-20: the grading hole is now the whole problem; no new kill.** OPEN.
- **Calibration (from established nodes only).** `leavitt-nonnegative-part-is-matrix-union-over-free-algebra` and
  `matrices-over-free-fields-have-no-trdeg-two-subfields` are both ESTABLISHED. Together they say `L_(>=0)` (and, by the
  involution, `L_(<=0)`) contains no two commuting independent elements over any field. So the conclusion of
  `leavitt-polynomial-pairs-move-to-the-nonnegative-part` is always false. That claim is now *equivalent* to
  `leavitt-algebras-contain-no-two-variable-polynomial-ring`, not a step towards it. The route
  `leavitt-rank-one-from-free-field-matrices-and-degree-reduction` has stopped being a decomposition: its only open
  prerequisite is its target, restated. Work on mechanism (i) should attack Q_2 directly. The "grading half" is not
  easier, and the w17 isotropy-lag kill of regradings already covers all residual pairs.
- **Thompson-unit YES witnesses: dead, with an explicit relation.** Take `Z^2 = <a, b> <= V ⊂ L^x`. Every point of
  `{0,1}^ω` lies in `int Fix(h)` for some `h ≠ 1` in `Z^2`:
  - on the torsion part a power of `a` is locally trivial;
  - at an attracting or repelling periodic point, the germ group is `Z`, so `Z^2` has a germ-trivial element;
  - that element fixes a neighbourhood of the periodic point, and by commutation it fixes the whole basin.
  By compactness finitely many `h_i` suffice, and then `Π_i (1 - h_i)` vanishes at every groupoid arrow (pair
  `S` with `S Δ {i}`). So `F_2[Z^2] -> L` is never injective. This is subsumed by
  `leavitt-thompson-units-have-finite-centralizer-rank` and is recorded only as a check on it.
- **Saturation of w17's singular set.** For any nonzero ring `B` receiving `L`, the set of elements of `k[a, b]`
  invertible in `B` is a saturated multiplicative set, because `qr` invertible and `qr = rq` give two-sided inverses
  of `q` and `r`. Hence the universally singular set `S` of `leavitt-polynomial-pairs-contain-a-universally-singular-element`
  satisfies `S·k[a, b] ⊆ S ∪ 0`, and `S ∪ 0` is an intersection of unions of primes.
- **Where it dies.** A local-Koszul upgrade would localize at `k[a, b] ∖ m` and run the Koszul resolution of
  `R/m` through `B ⊗_R -`. That needs `B` flat over `R = k[a, b]_m`, which fails at zero divisors, and
  zero divisors are exactly what `S` may contain. Nothing here selects which prime carries `S`.

1. **Refuted by Hochschild dimension (swarm-0917-w18c-w18c-bh-follow, 2026-09-19).** The claim is
   false at `G = Z^6`.
   - `polynomial-rank-is-at-most-hochschild-dimension` (ESTABLISHED, new): an algebra of Hochschild
     dimension `d` has no `d + 1` commuting algebraically independent elements. The proof bounds
     `l.gl.dim(A ⊗ k(y))` from below by a diagonal Koszul complex on `a_i - y_i`, and from above by
     `hd(A)`.
   - `cantor-crossed-hosts-of-finite-cd-have-bounded-polynomial-rank` (ESTABLISHED, new):
     `hd(LC(X)) <= 1` and `hd(A ⋊ P) <= hd(A) + cd(P)`. So `hd(B_Ω ⊗ L_∂) <= 3 + 2 = 5`, uniformly
     in `Ω` and `d`.
   - `F_2[Z^6] ⊇ F_2[x_1..x_6]` therefore has no embedding. `Z^6` is decidable. So
     `refuted_by: [cantor-crossed-hosts-of-finite-cd-have-bounded-polynomial-rank]`, and route
     `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts` is invalidated.
   - The body line **OPEN.** above is stale. It is left for the orchestrator, because only the
     frontmatter and Attempts may be edited.
   - Class kill: every host `LC(X) ⋊ P` with `cd(P) < ∞` misses `F_2[Z wr Z]`.
   - The Z^4 test (bound 5 against rank 4) is not settled by this.
