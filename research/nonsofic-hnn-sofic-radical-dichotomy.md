---
rg: 2
id: nonsofic-hnn-sofic-radical-dichotomy
kind: claim
title: A nonsofic HNN extension either has sofic radical meeting the base, or has a free sofic radical and a coset-inseparable base element
distinct_from:
  magnus-piece-meets-nontrivial-linton-radical: that says the Linton radical R meets the Magnus piece, which kills amenable/solvable fold targets. This concerns the sofic radical (the kernel onto the largest sofic quotient), which is contained in every kernel onto a sofic group and is trivial exactly when the group is sofic. It turns the whole nonsoficity of a witness into one of two named structural shapes.
  rigid-magnus-groups-have-sofic-separating-quotients: that is a positive route that needs one sofic quotient to be both base-injective and separating. This is the forced negative biography. Base-injectivity is equivalent to the sofic radical missing the base, so a witness with that property must lose separation in every partitioned model, not only in quotients.
  nonsofic-one-relator-relator-has-primitivity-rank-two: that constrains the relator word of a witness. This constrains how the sofic radical of the witness sits in a Magnus splitting.
  no-magnus-hierarchy-one-relator-groups-sofic: that is the affirmative hierarchy statement. This is the list of the only two ways a single Magnus step can fail, derived from a new HNN criterion.
  hnn-folds-into-free-coset-wreath: that is a sufficient condition through a coset wreath. This is a necessary dichotomy, and its case (ii) is where that corollary's coset-action hypothesis has to fail in its strongest, model-level form.
artifacts:
  - research/nonsofic-hnn-sofic-radical-dichotomy-proof.md
---

ESTABLISHED (written proof, unreviewed). REDUCTION, one direction only: it lists
properties that every nonsofic witness is forced to have.

Let `G = HNN(H; A -> B)` with `H`, `A`, `B` finitely generated, and let `T` be
its Bass--Serre tree. The **sofic radical** `N = Rad_sof(G)` is the intersection
of the kernels of all homomorphisms from `G` to sofic groups. `G/N` is sofic,
and `N = 1` iff `G` is sofic. Conditions (I) and (II) are as in
[[random-labeling-hnn-soficity-criterion]].

**Theorem.** (I) holds iff `N ∩ H = 1`. Hence, if `G` is not sofic, exactly one
of the following holds.

* **(i) The radical meets the base.** `N ∩ H != 1`. Every homomorphism from `G`
  to a sofic group kills a nontrivial element of `H`. Equivalently, no
  approximate model of `G` is free on `H`-words. This holds even when `H` is
  itself sofic.
* **(ii) The radical is free, and separation fails.** `N` is a nontrivial
  **free** group acting freely on `T`. `Q = G/N` is a sofic group into which `H`
  embeds, with `t̄ Ā t̄^(-1) = B̄`. Some nontrivial Britton-reduced word dies in
  `Q`. There is `h in (H \ A) ∪ (H \ B)` such that for every `δ > 0` there are
  `R, ε` with: every `(R, ε)`-model of `G`, with a partition that the
  generators of `A` preserve up to `ε`, separates `h` on the relevant side at
  fewer than `δ` of its points. In particular:
  * `ψ(h)` lies in `ψ(A)` (resp. `ψ(B)`) for every homomorphism `ψ` of `G` onto
    an amenable group;
  * `Q` is not amenable;
  * `G` is a free-by-sofic group that is not sofic.

**Minimal one-relator witness.** A nonsofic one-relator group is torsion-free,
because one-relator groups with torsion are virtually special. Up to the
standard Magnus--Moldavanskii embedding it is, or embeds into, an HNN extension
`HNN(B_0; F_- -> F_+)`. Here `B_0` is a one-relator group lower in the
hierarchy and `F_±` are free Magnus subgroups, and soficity passes to
subgroups. A witness of minimal hierarchy length has sofic `B_0`, and falls into
(i) or (ii) for this splitting.

* **Constructing (i)** means forcing `G`'s relations, through the stable letter,
  to kill a Magnus-piece element in every sofic image. That element must survive
  in `B_0`'s own sofic approximations but be incompatible with conjugating `F_-`
  onto `F_+` by a permutation.
* **Constructing (ii)** means some `h` outside a Magnus subgroup is
  asymptotically coset-inseparable: at fine enough scales every partitioned
  permutation model separates it on a vanishing fraction of points. This
  implies the failure of amenable separation already forced by
  [[magnus-piece-meets-nontrivial-linton-radical]]; whether it is strictly
  stronger is not decided here.

What is not proved: that (II) follows from soficity of `G`. If it did, case (ii)
would collapse to "(II) fails", and the dichotomy would become an equivalence.
