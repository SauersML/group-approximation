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
