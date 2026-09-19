---
rg: 2
id: mod-s2-torelli-positive-relations-have-bounded-mass
kind: claim
title: Every finite-index preimage of a subgroup of Sp_4(Z) kills a positive product of at most K separating twists with exponent sum prime to 3
distinct_from:
  mod-s2-induced-torelli-characters-have-positive-relation-floors: that proves the floor 1/(3 A_+) for each level and computes the base; this is the uniform bound sup A_+ < infinity, which is open.
  deligne-congruence-monomial-models-need-growing-defect: that uses transferred block cycles, whose value is divisible by 3 at q = 3; this asks for short positive relations that are not transfers.
---

**OPEN.** Notation as in `mod-s2-induced-torelli-characters-have-positive-relation-floors`. There is `K`
such that for every finite-index `Gamma' <= Sp_4(Z)` there are separating curves `s_1, ..., s_k` and
exponents `n_j >= 1` with the following properties:
- `sum_j n_j <= K` and `3 not| sum_j n_j`;
- the class of `t_(s_1)^(n_1) ... t_(s_k)^(n_k)` in `H_1(Lambda)` is trivial, where `Lambda = pi^(-1)(Gamma')`.

Equivalently, `sup_(Gamma') A_+(Gamma') < infinity`. By (Mono) it suffices to check a cofinal family,
for example the principal congruence subgroups `Gamma(N)`.

**Why it matters.** By (RF) it gives the uniform operator-norm floor `2 sin(pi/(3K))` for every
representation of `Mod(S_2)` induced from a character of a finite-index subgroup containing the Torelli
group. That is the Torelli-abelian induced class of `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`.
By (RF), `K` is at least `1/(3D)` at every level. The base forces `K >= 5`, and the level-4 census value
`1/30` reported on the live bus forces `K >= 10`.

**How it can fail.**
- *Divisibility.* For some tower, every positive relation has `3 | sum n_j`, as the transfer relations
  do when `3` divides the index.
- *Mass growth.* Positive relations prime to 3 exist, but their minimal mass grows.
- Either failure alone does not refute the gap, because (TD) allows non-positive and non-single
  certificates. The (TD) minimum can stay positive through many long relations, since the flatness
  constant grows with `r`.

## Attempts
- **2026-09-18, swarm-0917-w13-w13-deligne-break: posed.** The only positive relations constructed are
  transfers, of mass `5 [Sp_4(Z) : Gamma']`. A short positive relation must come from `H_2(Gamma')`
  classes supported near a single splitting orbit. Candidates are lifts of lantern or chain relations in
  `Gamma'`, which are not tested.
