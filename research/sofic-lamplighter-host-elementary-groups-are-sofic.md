---
rg: 2
id: sofic-lamplighter-host-elementary-groups-are-sofic
kind: claim
title: For every finitely generated infinite sofic group Δ, EL_3 over the binary crossed product of the lamplighter action of Z/2 ≀ Δ on 2^Δ is sofic
distinct_from:
  sofic-groups-embed-in-simple-kazhdan-sofic-groups: that asks for some infinite simple Kazhdan sofic envelope of each sofic group; this asks for soficity of one concrete host family, which supplies such envelopes by route sofic-envelope-from-sofic-lamplighter-host.
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that is the LEF acting groups, where exact configuration-space models make the host LEF; this is sofic acting groups, where the host is not LEF as soon as the derived subgroup of Δ is not.
  sofic-lamplighter-bernoulli-crossed-products-have-rank-models: that embeds the ring in a rank ultraproduct, which gives linear soficity of the group; this asks for soficity in the normalized Hamming metric.
  sofic-non-lef-infinite-simple-kazhdan-group-exists: that asks for one example; this claim at a single Δ with non-LEF derived subgroup, for instance the half-line overgroup of BS(2,3), would give one.
  free-minimal-subshift-elementary-groups-are-sofic: that is Z^2 subshifts of finite type, with an amenable acting group and a free action; this is a topologically free action of an arbitrary sofic acting group.
  column-model-kazhdan-cut-downs-certify-only-lef: that rules out one family of candidate approximations; this asks whether any approximation exists.
---

**OPEN.** Let `Δ` be a finitely generated infinite sofic group, and let `L = Z/2 ≀ Δ` act on `2^Δ`: `Δ` by shifts,
and the flip `a` at the coordinate `e`. Put `R_Δ = LC(2^Δ,F_2) ⋊ L`. Then `EL_3(R_Δ)` is sofic.

**Known about the host.**
- `EL_3(R_Δ)` is infinite, finitely generated, simple and Kazhdan. It contains `[Δ,Δ]` (route
  `sofic-envelope-from-sofic-lamplighter-host`, steps 2, 3 and 5).
- It is `F_2`-linear sofic, by `sofic-lamplighter-bernoulli-crossed-products-have-rank-models` and the projective
  transfer in step 4 of `sofic-groups-simple-kazhdan-linear-sofic-envelope-proof`. That step uses only that `Δ` is
  finitely generated, infinite and sofic.
- It is LEF when `Δ` is LEF (`lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`), and not LEF when `[Δ,Δ]` is
  not.
- Its invariant random subgroups are trivial (`lamplighter-host-elementary-groups-have-trivial-irs`).

**Use.** The case `Δ = C(Γ)` alone, for every finitely generated sofic `Γ`, gives
`sofic-groups-embed-in-simple-kazhdan-sofic-groups` by route `sofic-envelope-from-sofic-lamplighter-host`. Soficity of
`EL_n(R_Δ)` for any `n ≥ 3` implies the case `n = 3`, since `EL_3` embeds in `EL_n` by blocks.

**Stakes.** At a single `Δ` with `[Δ,Δ]` not LEF, a positive answer gives a sofic infinite simple Kazhdan group that
is not LEF. A proof that sofic infinite simple Kazhdan groups are LEF would refute this claim at every such `Δ`.

## Attempts

- **LEF acting groups: true, and not the issue.** `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` uses exact
  configuration-space models over LEF models of `Δ`. Over a non-LEF `Δ`, the configuration-space models of
  `sofic-lamplighter-bernoulli-crossed-products-have-rank-models` are multiplicative only off the rows whose base points
  are bad. That is the rank-metric situation of the next bullet.
- **Rank models on vectors: dead** (`rank-models-give-no-hamming-models-through-vector-actions`,
  `gap-sofic-approximations-are-local-embeddings`).
  - The counting rank models fail multiplicativity on `o(N)` but nonzero rows.
  - An invertible matrix error `x` with `rk(x − 1) = r ≥ 1` fixes exactly a `2^(−r)` fraction of the vectors. So the
    induced permutations have Hamming defect at least `1/2` whenever the error is nonzero.
- **Kazhdan cut-downs of semisimple column models: dead** when `[Δ,Δ]` is not LEF (Corollary C of
  `orbitwise-gap-sofic-approximations-are-local-embeddings`).
- **Kazhdan cut-downs of column models through arbitrary finite image rings: dead** when `[Δ,Δ]` is not LEF
  (swarm lane, 2026-09-16).
  - `elementary-group-column-actions-have-orbitwise-gap` gives orbitwise gap `1/(2n²)` for every image algebra, radical
    allowed. So `column-model-kazhdan-cut-downs-certify-only-lef` applies to every assignment of the letters to
    matrices over `F_2`, with any almost invariant sets of vectors.
  - This closes target T5 of `research/artifacts/sk-sofic-almost-action-plan-2026-09-14.md`.
- **Permanence closure: dead** (`kazhdan-groups-in-sofic-permanence-closure-are-lef`). Finitely generated Kazhdan
  groups built from amenable and LEF groups by the operations listed there are LEF.
  - Caveat: a 2026 arXiv abstract (arXiv:2601.18742, Alekseev–Bradford, abstract only, unverified) concerns
    semidirect-product permanence of soficity. That operation is not in the list, and it is not analyzed here.
- **Ergodic centralizers: dead** (`kazhdan-ergodic-sofic-centralizer-forces-lef`). A sofic embedding of a non-LEF
  Kazhdan group must have a non-ergodic centralizer in the permutation ultraproduct.
- **Full groups of exactly modelled actions: dead** (`research/artifacts/sk-sofic-host-hamming-2026-09-13-part1.md` §4,
  Lemma E). Their finitely generated subgroups are LEF.
- **Lie-type finite quotients: partial, not settled** (artifact
  `research/artifacts/elementary-orbitwise-gap-any-finite-ring-2026-09-16.md` §5).
  - Let the cover `H = EL_3(F_2⟨B⟩)` act on genuine finite `H`-sets through finite simple quotients of Lie type.
    Transitive fixed-point ratios are bounded by primitive ones, and Liebeck–Saxl-type bounds (not read at source)
    would give a common gap, hence LEF.
  - The argument breaks for finite quotients with a unipotent radical, whose elements can act trivially on every
    primitive quotient.
- **Nonsofic mechanism: not analyzed (referee caveat, 2026-09-16).** Kun–Thom, arXiv:2608.06222 (abstract read
  2026-09-16), prove nonsoficity for some generalized wreath products `(⊕_(G/Λ) Z/2) ⋊ G` and doubles `G ∗_Λ G`. Here
  `Λ < G` is not normal, both groups are Kazhdan, and `{g : gΛg^(−1) ≤ Λ}` generates `G`. Whether that mechanism
  applies to any subgroup of `EL_3(R_Δ)` was not checked.
- **What remains.** By Theorem O and the Kazhdan cutting lemma, a sofic approximation of a non-LEF host must be one of
  two kinds.
  - (M1) Not a Kazhdan cut-down of any genuine `H`-set with a common orbitwise gap. Then the Steinberg relations of
    the cover fail on a vanishing but nonzero set of points.
  - (M2′) A cut-down of genuine finite `H`-sets without a common orbitwise gap, and these are not column models.
    Candidates are coset spaces with non-vector stabilizers, affine actions, and tensor or adjoint representations.
