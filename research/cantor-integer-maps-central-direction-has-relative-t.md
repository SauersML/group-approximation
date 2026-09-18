---
rg: 2
id: cantor-integer-maps-central-direction-has-relative-t
kind: claim
title: "The pair (C(C,Z) ⋊ V, <1_C>) has relative property (T): every cnd function on C(C,Z) ⋊ V is bounded on the constant functions Z·1_C"
distinct_from:
  cantor-integer-maps-by-v-are-not-a-t-menable: that denies the Haagerup property; this is a strictly more specific statement that implies it (a proper function is unbounded on the infinite subgroup <1_C>), and it is the weakest relative-(T) statement for a subgroup of C(C,Z)
  cantor-integer-maps-central-growth-criterion: that is the established equivalence between failure of this claim and almost invariant vectors with no 1_C-invariant vector; this is the open assertion that no such representation exists
  extractable-character-spectra-carry-no-almost-invariant-vectors: that establishes this claim for the extractable spectral parts of all cnd functions (with an explicit bound); this is the full statement, whose remaining case is scale-incoherent characters
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that proves boundedness of 1_C for commensurating (wall) cnd functions only; this asks it for all cnd functions
refuted_by:
  - cantor-integer-maps-by-v-have-haagerup-property
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

**Statement.** Let `G = C(C,Z) ⋊ V` and `z = 1_C`. For every cnd function `ψ` on `G`,
`sup_M ψ(z^M) < ∞`.

**Equivalent forms.** By `cantor-integer-maps-central-growth-criterion`, the following are
equivalent to the statement:
- no unitary representation of `G` without nonzero `π(1_C)`-invariant vectors has almost
  invariant vectors;
- for every cocycle, the restriction to `ker(π(1_C) − 1)^⊥` is a coboundary.

By `extractable-character-spectra-carry-no-almost-invariant-vectors`, it holds for the part of
any cocycle carried by finitely atomic, bounded-phase-variation or `F`-regular characters.

**Why it matters.**
- It implies that `2V`, and every `nV` with `n ≥ 2`, is not Haagerup, since
  `G ≤ 2V ≤ nV`.
- Its negation is necessary for Problem B(Z) and for Haagerup of `nV`. So a positive answer
  must construct almost invariant laws on scale-incoherent characters with `χ(1_C) ≠ 1`.

**Status.** OPEN. The attempt to close it is recorded under
`cantor-integer-maps-sup-norm-is-cnd-dominated`, Attempts, 2026-09-17.

## Attempts

- **2026-09-17 (swarm-0917-w5-nv-cocycle): paradoxical push-forward along an extraction (dies
  at scale-incoherent characters).**
  - The three moves `0↦00`, `0↦01` and the first-letter swap make any probability measure on
    `C` almost invariant under them paradoxical.
  - This kills every spectral part carried by a `V`-invariant character set with an equivariant
    Borel map to `Prob(C)`
    (`extractable-character-spectra-carry-no-almost-invariant-vectors`).
  - It dies where no location can be read off equivariantly: characters with infinite phase
    variation and no convergent `F`-variation. The kill uses only three group elements, so it
    cannot see correlations across scales. An argument there must use unbounded families of
    elements of `V`, for example the relative-(T) generation of `C(C,Z)` by conjugates.
- **Linear-response designs (die).** Take vectors whose `1_C`-phase is `e(θm)` on mass at
  charge `m`, with invariance defect `o(θ)`. A charge inequality from the same push-forward,
  `⟨|arg π(1_C)| η, η⟩ ≤ 5δ + 3ε²`, blocks them. It does not constrain growth rates, so it does
  not decide the claim.
- **Quasimorphisms and congruence quotients (die).**
  - Every homogeneous quasimorphism of `G` vanishes on `A`, so `scl(1_C) = 0` gives nothing.
  - In `C(C,Z/N) ⋊ V` the image of `1_C` has finite order, so it can carry no growth witness.
- **2026-09-17 (swarm-0917-w6b-w6b-nv-break): independent or mixing witness laws (die;
  class-kill).**
  - Established `cantor-central-witnesses-have-long-range-dependence`. Suppose a witness
    `ξ` is `ε`-almost invariant with no `1_C`-invariant vector, and `(u, v)` is a pair of
    disjoint, non-complementary cones. Then the spectral law keeps the phases `χ[u]` and `χ[v]`
    at conditional TV-dependence at least `(1 − ε − 50Lε)/8`, given any `V`-invariant function.
    Here `L` is the word length of four moving elements.
  - **Invariant:** `χ[0] = χ[00] + χ[01]`. Two prefix moves turn independence into
    `ν ≈ ν * ν` in total variation.
  - **Where every member dies:** `ν̂` cannot leave `1`, since it stays near `{0, 1}` with steps
    less than `1`. So `χ[0]` and `χ[1]` have atoms near mass `1` at `0`, which forces
    `χ[C] = 0`.
  - **Class killed:** independent-subtree, finite-range or mixing random characters, wrapped
    Gaussian charges with small correlations, and random cone products with rarely included
    common ancestors.
  - **Not ruled out:** witnesses with long-range coupling that is not a `V`-invariant function
    of `χ`, for example a random scale shifted by `V`.
  - **Refutation route (not recorded as a node).** Suppose some co-amenable `H ≤ G` contains
    `1_C` with `(H, Z·1_C)` not relatively (T), for example with `ψ : H → R` and
    `ψ(1_C) ≠ 0`. Then this claim fails: induce `e^{2πitψ}`, use Fell continuity of induction,
    and note that `1_C` acts by a scalar.
    - Obstruction: take a section cocycle `c(g, x)` of `G/H`. If `ψ∘c(s, ·)` is bounded for the
      generators `s`, averaging `ψ∘c` with the invariant mean gives a homomorphism `G → R`
      that is nonzero on `1_C`. This is impossible because `G` is perfect.
    - So such `H` must have unbounded transfer.
- **2026-09-17 (swarm-0917-w7-w7-nv-last1): Gaussian designs of every correlation structure (die;
  class-kill).**
  - Established `cantor-central-gaussian-scale-mixture-witnesses-die`. No sequence of wrapped
    laws `e∘(m + √s·Y)` is `V`-almost invariant, tends to `δ_0` and keeps `χ(1_C) ≠ 1`. Here `Y`
    is a centred Gaussian random homomorphism with any covariance, `m` is a deterministic mean and
    `s > 0` is an independent random scale. Every such sequence ends with `χ(1_C) = 1` a.s.
  - **Invariant:** quadratic inclusion–exclusion of the covariance. Near `0` the lift mod 1 is
    harmless. The scale-free angular laws of ordered pairs of disjoint cones are then forced to one
    limit with variance ratio `1` and correlation `−1/2`.
  - **Where every member dies:** the pair `(U_1⊔U_2⊔U_3, U_4)`, whose variance ratio must be
    `1` but equals `3 − 3 = 0`. When the Gaussian part degenerates, the mean is a
    `V`-invariant character on the cones and additivity forces `χ(1_C) = 1`.
  - This kills the survivor "random scale shifted by `V`" of the previous attempt for Gaussian
    shapes, and it makes the heuristic white-noise kill in
    `cantor-integer-maps-by-v-have-haagerup-property` rigorous.
  - **Remaining classes:**
    - mixtures over a random covariance *shape* (angular mixtures are not identifiable);
    - random means;
    - jump-type (compound Poisson) laws. These are the canonical `e^{−tψ}` witnesses, since the
      Gaussian part of every cnd `ψ|_A` vanishes by artifact §3(e).
- **2026-09-18 (swarm-0917-w7-w7-nv-break, reframing): co-amenable induction witnesses (die
  unless `V` has a fixed-point-free amenable action; class-kill).**
  - Established `central-induction-witnesses-need-amenable-v-action`, which kills the w6b refutation
    route above.
  - *Class.* `Ind_H^G χ_t` with `H` co-amenable, `1_C ∈ H`, `χ_t → 1` and `χ_t(1_C) ≠ 1`.
  - *Invariant.* The constancy partition `P(f)`. It is quasi-equivariant under the affine `V`-action on
    `A/Z·1_C`, and it has `2^d` cones on depth-`d` checkerboards.
  - *Where every member dies.*
    - If `H` maps onto `V`, then `H ∩ A` is a `V`-submodule, so it lies in `Z·1_C` or contains `nA`.
    - In the first case, the transfer theorem of
      `thompson-v-finitary-structure-stabilizers-are-not-co-amenable` puts positive mean on bounded
      partitions, and disjoint checkerboard translates make that mean zero. So there is no mean.
    - In the second case, `1_C` has order dividing `n` in `H^ab`, since `A` is generated by the
      elements `v·f − f`.
    - What is left is a proper co-amenable image `p(H) < V`. That is the open
      `thompson-v-has-a-fixed-point-free-amenable-action`, and it would make `V` sofic.
  - *Not ruled out.* Non-induced witnesses; induction of higher-dimensional representations from a
    co-amenable `H ⊇ nA`, which is the original problem again; and a proper co-amenable subgroup of `V`.
- **2026-09-18 (e2-w2-nv-relative-t, heretic): sparse (rarely active) witness laws (die;
  class-kill at `1/2`, not `3/4`), and one tool left behind. Refereed 2026-09-18: refuted as
  stated, `cantor-central-witnesses-have-active-cone-phases` returned to OPEN.**
  - **What is actually proved.** For every unitary representation, every unit vector with defect
    `ε` and every `M ∈ Z`, `|1 − Φ(M·1_C)| ≤ 4(1 − Re Φ(M·1_{[0]})) + 40Lε`. Averaging in `M` and
    applying Wiener's theorem on `T`,
    `μ{χ[C] = 0} ≥ 4·μ{χ[U] = 0} − 3 − 40Lε − 16|h|_S ε` for a proper clopen `U` and `h ∈ V` with
    `h[0] = U`. So in any witness the phase of a fixed cone of depth `o(1/ε)` is nonzero with
    probability at least `1/4 − o(1)`. The uniform-in-`U` form with a single absolute constant,
    which the node's title asserted, is **not** proved: the error grows with the depth of `U`.
    That gap is now `cantor-cone-phase-atom-comparison-is-depth-uniform`, required by the route.
  - **The class-kill is real but the threshold was wrong, and the mechanism credited was wrong.**
    Referees derived, from the same two imports and nothing else, the strictly stronger
    `μ{χ[C] = 0} ≥ 2·μ{χ[U] = 0} − 1 − O(ε)`: finite additivity gives
    `χ[C] = χ[[0]] + χ[[1]]`, so `{χ[[0]]=0} ∩ {χ[[1]]=0} ⊆ {χ[C]=0}`; inclusion–exclusion gives
    `μ{χ[C]=0} ≥ μ{χ[[0]]=0} + μ{χ[[1]]=0} − 1`; and transport along the single first-letter swap
    `b` gives `μ{χ[[1]]=0} ≥ μ{χ[[0]]=0} − 4|b|_S ε`. No Möbius identity, no Cauchy–Schwarz, no
    Wiener theorem. `2p − 1 ≥ 4p − 3` for every `p ≤ 1`. So:
    - the class killed is `p = μ{χ[U] = 0} > 1/2`, not `p > 3/4`;
    - the activity a witness must have is `μ{χ[U] ≠ 0} ≥ 1/2 − O(ε)`, not `1/4 − o(1)`;
    - every member of the killed class dies at the **two-piece** identity, not at the three-piece
      Möbius identity;
    - "the constant `4` is sharp and the calibration is exact" is **false**. The cone-product
      family of `cantor-integer-maps-pair-lacks-relative-property-t` sits at `(1,1)` as
      `p_incl → 0`, and `p_C = c·p_U − (c−1)` passes through `(1,1)` for every `c`, so it
      calibrates nothing; and `c = 2` beats `c = 4` outright.
  - **What survives.** The *pointwise* inequality is not subsumed — for small `1 − Re u_M` it
    beats the two-piece triangle bound `2√(2(1 − Re u_M))`. Corollary 3, near-positivity of the
    cone-phase transform `|Im Φ(M·1_U)| ≤ 4(1 − Re Φ(M·1_U)) + O(ε)` with no `V`-ellipticity
    hypothesis, is untouched. The mechanism genuinely uses the non-unimodularity of `V`
    (transitivity on proper clopen sets of *different* Bernoulli measure), six times, and fails
    for level-preserving tree automorphisms — so it is not a soft argument.
  - **Invariant:** `p = μ{χ[U] = 0}`, the atom at `0` of the cone-phase law, equivalently the
    Cesàro limit of `Re Φ(M·1_U)`. It is the same for every proper clopen `U` up to `O(|h|_Sε)`,
    not up to an absolute `O(ε)`. It is read by the elementary two-piece argument as well, so the
    novelty of the invariant was overstated.
  - **No hypotheses:** no independence, no moment condition, no exact invariance, no equivariant
    extraction. The bound therefore also holds on scale-incoherent characters.
  - **Not ruled out (corrected frontier):** diffuse witnesses with `p ≤ 1/2` — the band
    `(1/2, 3/4]` that this entry originally advertised as surviving is already dead, so no lane
    should be pointed at it. In particular compound Poisson laws whose Lévy measure gives
    infinite mass to `{χ[U] ≠ 0}` (there `p = 0` and both inequalities are vacuous). These are
    the canonical `e^{−tN}` survivors of the Gaussian kill.
  - **Tool left behind (adoptable).** *Ruler partitions.* For `n ≥ 2`,
    `P_n = {[1], [01], …, [0^{n−2}1], [0^{n−1}]}` is a partition of `C` into `n` cones such that
    every permutation of the parts is realized by an element of `V` with `n` pieces, so `n`-fold
    exchangeability of the phases costs invariance defect `poly(n)·ε` instead of the `2^n·ε` of
    the depth-`n` dyadic partition, while the parts still sum to `1_C`. This removes the cost
    obstruction to approximate de Finetti arguments on this node.
  - **Where the ruler route dies anyway (recorded dead end).** De Finetti plus the merge relation
    makes the directing measure idempotent, hence `Haar(H)`, and `Re Φ(1_U) ≥ 1 − ε²/2` forces
    `H = {0}` with probability near `1`; the conclusion needed is "`χ[P] = 0` for every
    `P ∈ P_n`", which with `Σ_P χ[P] = χ[C]` would give the atom. That last step fails for a
    reason that is not quantitative slack: an approximate argument concludes only that each
    `χ[P]` is *small*, while the negation of this claim asks only that `χ[C]` be *nonzero*, not
    large, and a sum of `n` small nonzero phases is still nonzero. So the blocker for approximate
    de Finetti proofs here is not the cost of exchangeability but the exactness of the event
    `{χ[C] = 0}`; a proof must pass through an exact-vanishing device such as a Cesàro average in
    the frequency, or a paradoxical decomposition.
