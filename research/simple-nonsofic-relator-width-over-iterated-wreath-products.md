---
rg: 2
id: simple-nonsofic-relator-width-over-iterated-wreath-products
kind: claim
title: A finitely presented simple nonsofic group has relator width bounded independently of depth over iterated permutational wreath products
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that bounds the width over symmetric, alternating, sporadic and bounded-rank Lie type groups, which have chief length one; this asks for a bound over iterated wreath products, whose chief length is the depth and grows without bound.
  perfect-group-relator-width-over-nilpotent-groups: that bounds the width over nilpotent groups, including iterated wreath products of cyclic p-groups, using only perfection; this asks for the non-nilpotent case, where the lower central series trick has no analogue.
  non-linear-sofic-simple-groups-bounded-width-in-classical-groups: that is the other remaining family, classical groups of unbounded rank; this is the family of unbounded chief length.
---

**OPEN.** Let `G = <X | R>` be an infinite finitely presented simple group that is not sofic.
For a finite group `Q` and `a in Q^X` let `w_Q(a)` be the least `K` such that every generator
`a_x` is a product of at most `K` `Q`-conjugates of relator values `r(a)^(+-1)`.

**Claim.** For every `m` there is `K(G, m)` such that `w_Q(a) <= K(G, m)` for every iterated
permutational wreath product `Q = T_1 wr T_2 wr ... wr T_d` of transitive groups
`T_i <= Sym(m_i)` with `m_i <= m`, every depth `d`, and every `a in Q^X`.

**Payoff.**
- **True.** The deep wreath family, which is where Glebsky's extension proofs build their models,
  is excluded as a target for weak models of `G` with any bi-invariant lengths. For the binary
  Leavitt unit group this removes one of the two families left open on
  `fg-simple-weakly-sofic-groups-are-sofic`.
- **False.** Then `G` is weakly sofic (`glebsky-rivera-w-sofic-criterion`, with simplicity as in
  Section 0 of `simple-group-support-and-semisimple-rank-models-collapse-proof`), so `G` is a finitely
  presented simple weakly sofic nonsofic group, refuting `fg-simple-weakly-sofic-groups-are-sofic`.

## Attempts

- **Bounded depth or bounded exponent carries no information.** For fixed `d` and `m` the groups
  `Q` are finitely many, so (E1)--(E2) of `simple-group-relator-width-in-finite-simple-targets-proof`
  bound the width. More generally the width is bounded over any class of finite groups whose
  `|X|`-generated members have bounded order (width can only drop under quotients, and every such
  member is a quotient of one finite relatively free group). So unbounded width needs unbounded
  exponent, which the iterated wreath products have.
- **Direct products and the top-level reduction.** A *template* for `x` is a fixed word in `R^(+-1)`
  whose letters can be conjugated to give `a_x`. A template valid for every tuple in a class stays
  valid over direct products of that class, with conjugators chosen coordinatewise; trivial coordinates
  accept every template. In `Q = W_d` with nonabelian simple `T` at every vertex, the least level at
  which `<a>` acts nontrivially is also the least level at which some relator value acts
  nontrivially: above it the tuple satisfies every relator exactly, and `G` has no finite quotient.
  So `a` lies in the stabilizer of the last level it fixes, a direct product of subtree groups. So
  templates reduce the claim to tuples that act nontrivially at the top.
- **Every length that sees only supports collapses.** Lengths that are monotone subadditive functions
  of the support sizes in any family of actions, for example weighted sums of normalized supports on
  all tree levels, give no weak models (Lemma 1.2 of
  `simple-group-support-and-semisimple-rank-models-collapse-proof`, applied level by level). So
  the claim is about capped conjugation lengths, not about the tree geometry.
- **Where the level-by-level correction dies.**
  - *Setup.* Lift the top-level width, then correct the defect in `St(j) / St(j+1) = T^(Omega_j)` level
    by level, by inserting conjugate pairs `r, d r^-1 d^-1` with `d` in `St(j)`. At a vertex `v` fixed by
    `r(a)` the pair contributes the commutator `[t_v(r), d_v]` with the local label. Along a cycle `C`
    of `r(a)` at level `j`, it contributes anything with twisted cycle product `[z_C, h]`, where `z_C` is
    the return label of `r(a)` along `C`.
  - *The obstruction.* Where return labels are trivial, cycle products cannot be corrected at level
    `j`. Conjugators come from the imprimitive group `W_(d-1)`, not `Sym(Omega_j)`. So the
    covering-by-translates step of the symmetric case does not transfer, and the naive bound grows
    linearly in `d`.
  - *What is missing.* Unlike the lower central series, `[W_d, St(j)]` is not contained in `St(j+1)`.
    So the nilpotent trick of reusing one pair per relator with compounding conjugators does not
    apply as it stands.
- **A lower-bound tool for a refutation.** `l(g) = log|g^Q|` is a bi-invariant pseudo-length, since
  `(gh)^Q ⊆ g^Q h^Q`. So `w_Q(a) >= log|a_x^Q| / max_r log|r(a)^Q|`. A refutation needs tuples whose
  generator classes are exponentially larger than every relator class. By Liebeck--Shalev this
  cannot happen in a simple `Q` with large relator classes.
