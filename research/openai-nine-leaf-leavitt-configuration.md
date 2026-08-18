---
rg: 2
id: openai-nine-leaf-leavitt-configuration
kind: claim
title: The nine-leaf Leavitt configuration satisfies every hypothesis of the expander-matching criterion
distinct_from:
  openai-expander-matching-criterion: That is the general criterion, quantified over compressing triples and mentioning no ring; this is one explicit triple over the binary Leavitt algebra, and it asserts only that the hypotheses hold, not that anything is nonsofic.
  universal-leavitt-el4-nonsofic: That is this repository's own endpoint over the same algebra, at rank four, with a two-relator corner witness and its own compression setup; this is the chapter's rank-nine configuration with Thompson's `V` as witness and two prefix replacements as compressors.
  leavitt-cylinder-swaps-generate-thompson-in-el: That is the general membership lemma for cylinder swaps in an elementary prefix group; this is the configuration that uses it twice, together with the two compression tables and the generation statement.
  leavitt-gl-equals-el-and-perfect-unit-group: That is the rank transport and perfectness, pure algebra about `GL` and `EL`; this is a specific subgroup triple with commutation, intersection and compression properties, assembled for a criterion.
artifacts:
  - official/counterexample.tex
---

ESTABLISHED.  Section 3 of the OpenAI nonsofic chapter, over
`R = L_(F_2)(1,2)`.  Take the three prefix blocks

    alpha = (000, 001, 01),
    beta  = (1000, 1001, 101),
    nu    = (1100, 1101, 111),

whose cylinders partition `[0]`, `[10]` and `[11]`, and let `D` be their
concatenation -- a complete nine-leaf code.  Put

    G = EL_D(R) =~ EL_9(R),   Gamma = EL_alpha(R) =~ EL_3(R),   J = V_(1000).

Define `u, v` in `V <= G` by the prefix tables

    u : alpha_i -> alpha_i 0,   beta_i -> alpha_i 1,   nu_i -> zeta_i
    v : alpha_i -> alpha_i 0,   beta_i -> zeta_i,      nu_i -> alpha_i 1

with `zeta = (100, 101, 11)` partitioning `[1]`.  Then:

* `Gamma <= G <= R^x`, both infinite, finitely generated, and both with
  Kazhdan's property (T);
* `u Gamma u^(-1) = v Gamma v^(-1) = EL_((alpha_1 0, alpha_2 0, alpha_3 0))(R)
  <= Gamma`;
* `G = <Gamma, u, v>`;
* `[Gamma, J] = 1`, `Gamma cap J = {1}`, so `Gamma x J <= G`;
* `u J u^(-1) = V_(0001) <= Gamma`;
* `J =~ V`, Thompson's group.

These are exactly the hypotheses of [[openai-expander-matching-criterion]]
with `t_1 = u` and `t_2 = v`.

## What each piece is doing

`Gamma` lives on the cylinder `[0]` and `J` on the disjoint cylinder `[1000]`,
which is the whole of the commutation and intersection statements: `g - 1` and
`j - 1` sit in the orthogonal corners `e_0 R e_0` and `e_1000 R e_1000`, so
their products vanish both ways and a common element would be `1`.

The two compressions are not interchangeable and neither is redundant.  Both
send `[alpha_i]` into `[alpha_i 0]`, so both compress `Gamma`; but `u` sends
the `beta`-block into `[alpha_i 1]` and the `nu`-block onto `[zeta_i]`, while
`v` does the reverse.  One of them alone recovers only the six leaves it
touches -- `<Gamma, u>` reaches `EL_((alpha,beta))(R)` and `<Gamma, v>`
reaches `EL_((alpha,nu))(R)` -- and the commutator identity across an
`alpha`-leaf is what joins a `beta`-leaf to a `nu`-leaf.  Two compressors,
nine leaves.

Only `u` is used for the obstruction: `u` carries `beta_1 = 1000` to
`alpha_1 1 = 0001`, so `u J u^(-1) = V_(0001) <= Gamma`.  `v` exists to make
`<Gamma, u, v>` the whole of `G`.

## Not needed, though true

`G = R^x` holds (Kun--Thom, arXiv:2608.06222, Corollary 4.4), and this
repository proves the same identification independently through
[[leavitt-gl-equals-el-and-perfect-unit-group]].  The chapter does not use it:
soficity passes to subgroups, so nonsoficity of `G` already gives
nonsoficity of `R^x`.
