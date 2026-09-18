---
rg: 2
id: random-labeling-hnn-soficity-criterion
kind: claim
title: Piece-labeled stable letters make an HNN extension sofic from base-free models plus coset-separating partitions
distinct_from:
  hnn-folds-into-free-coset-wreath: that needs one homomorphism into a sofic group that is injective on the base, separates the associated subgroups, and has a sofic coset action. This needs no quotient group and no action soficity. Freeness on the base and coset separation may come from two unrelated permutation models, and the separating model may kill the base entirely.
  rigid-magnus-groups-have-sofic-separating-quotients: that asks one sofic quotient to be injective on the Magnus piece and separating at once, which is what the Linton radical blocks for amenable targets. This splits the two requirements. Injectivity goes to models of the group itself, and separation goes to partitioned models with no freeness requirement.
  gkp-free-generalized-wreath-soficity: that is permanence for free generalized wreath products over sofic actions; this is a permanence theorem for HNN extensions with two distinct associated embeddings, proved directly by random permutations indexed by partition pieces.
  magnus-staggered-chain-sofic: that is the soficity claim for every Magnus chain; this is a general HNN criterion whose Magnus instance reduces that claim to one-window freeness plus coset separation, in one direction only.
artifacts:
  - research/random-labeling-hnn-soficity-criterion-proof.md
---

ESTABLISHED (written proof, unreviewed). Let `H` be finitely generated, and
let `φ : A -> B` be an isomorphism between finitely generated subgroups of `H`.
Put

    G = < H, t | t a t^(-1) = φ(a)  (a in A) >.

A **model** of `G` is a finite set `Y` with permutations for the generators of
`H` and for `t`. An `(R, ε)`-model is one in which every word of length `<= R`
that is trivial in `G` fixes at least `(1-ε)|Y|` points.

**(I) Base-free models.** For all `R, ε` there is an `(R, ε)`-model `X` of `G`
such that every word in the generators of `H`, of length `<= R`, that is
nontrivial in `H` fixes at most `ε|X|` points.

**(II) Coset-separating partitions.** For all `R, ε` there are an
`(R, ε)`-model `Y` of `G`, with stable-letter permutation `τ`, and a partition
`P` of `Y` with the following properties. Here `u` ranges over words of length
`<= R` in the generators of `H`.
* Each generator of `A` keeps all but `ε|Y|` points in their piece.
* If `u` is not in `A`, then `u(y)` lies in the piece of `y` for at most
  `ε|Y|` points.
* If `u` is not in `B`, then `u(z)` lies in the same `τ(P)`-piece as `z` for at
  most `ε|Y|` points.

No freeness is required in (II).

**Theorem.** (I) and (II) imply that `G` is sofic. Conversely, if `G` is sofic
then (I) holds.

**Construction.** On `X × Y × [M]`, `H` acts diagonally on `X × Y` and trivially
on `[M]`. The stable letter acts by

    t(x, y, j) = (τ_X x, τ y, π_(P(y)) j),

with an independent uniformly random permutation `π_P` of `[M]` for each piece.

Take a Britton-reduced word. Its `[M]`-coordinate is a reduced word in the
independent `π_P` at all but `O(Rε)` of the points `y`. At such a point, a fixed
reduced word of length `n` fixes a given `j` with probability at most
`n(n+1)/(M-n)`, by lazy revelation. Words of `t`-length zero are handled by (I).

**Amplification.** (II) holds as soon as each single `h` in `H \ A` (resp.
`H \ B`) is separated on a fraction at least `δ_h > 0` of points in some model,
uniformly in `(R, ε)`. Products of models, with product partitions, multiply
the non-separated fractions.

**Corollary (amenable separation).** Suppose:
* for every `h in H \ A` there is a homomorphism `ψ` from `G` onto an amenable
  group with `ψ(h)` not in `ψ(A)`;
* for every `h in H \ B` there is such a `ψ` with `ψ(h)` not in `ψ(B)`.

Then (II) holds. The model is a Følner set of the quotient, and the pieces are
the traces of right `ψ(A)`-cosets.

Hence `G` is sofic whenever (I) holds and amenable quotients separate as above.
In particular this holds when:
* some sofic group receives a homomorphism of `G` that is injective on each
  finite subset of `H`;
* amenable quotients of `G` separate the associated subgroups.

The two families of quotients are unrelated.

**Calibration.** `BS(1,2) = HNN(Z, Z -> 2Z)` is recovered. The cyclic models
`Z/N`, `N` odd, satisfy (I) exactly. Their only `A`-invariant partition is
trivial, however, so they fail (II) for `h = a`, which is not in `B`. The
Følner model of `BS(1,2)` itself supplies (II). This shows that (II) is a
genuine second input and not a consequence of (I).

## Application to the flagship

Consider a Magnus splitting `G = HNN(B_0; F_- -> F_+)` of a torsion-free
one-relator group. The theorem, together with the identity "(I) iff the sofic
radical of `G` misses the base", forces any nonsofic witness into one of two
shapes. These are recorded in [[nonsofic-hnn-sofic-radical-dichotomy]]:
* the sofic radical meets `B_0`;
* the sofic radical is a nontrivial free group, and some base element outside
  a Magnus subgroup is asymptotically coset-inseparable: at fine scales every
  partitioned permutation model separates it on a vanishing fraction of points.

What remains open is whether (II) follows from soficity of `G`. The necessary
direction is proved only for (I).
