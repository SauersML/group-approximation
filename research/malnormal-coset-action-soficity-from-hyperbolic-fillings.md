---
rg: 2
id: malnormal-coset-action-soficity-from-hyperbolic-fillings
kind: claim
title: If every hyperbolic group is sofic, every almost malnormal quasiconvex residually finite coset action of a hyperbolic group is sofic, so a nonsofic such action of a linear hyperbolic group yields a nonsofic hyperbolic group
distinct_from:
  relative-nonrf-target-iff-hyperbolic-nonrf: that transfers failure of residual finiteness of a relatively hyperbolic group to a hyperbolic filling; this transfers failure of soficity of a coset ACTION of a hyperbolic group, which may itself be sofic or linear, to a hyperbolic filling, and needs the double to control cosets rather than elements
  sofic-coset-action-makes-amalgam-double-sofic: that goes from a sofic action to a sofic double; this goes from sofic fillings to a sofic action, and uses the double only as a hyperbolic device detecting coset membership after filling
  sofic-coset-actions-pass-to-marked-colimits: that is the closedness theorem for marked pairs; this supplies, for every almost malnormal quasiconvex pair in a hyperbolic group, approximating pairs with hyperbolic ambient group and finite stabilizer
  nonsofic-hyperbolic-question-reduces-to-one-fixed-host: that moves the flagship between groups (LEH groups, quotients of one host); this moves it from groups to set actions of hyperbolic groups, where nonsofic examples are already known to exist in other hosts
  hyperbolic-local-embedding-kills-compression-certificates: that kills compression and commuting-pair certificates inside LEH groups; this opens a certificate class, nonsofic malnormal coset actions, that neither kill touches, because the ambient group may be linear and the stabilizer shares no infinite subgroup with its conjugates
---

**ESTABLISHED** through
`malnormal-coset-action-soficity-from-hyperbolic-fillings-proof`, modulo the
three imported theorems named there (Osin's Dehn filling, Bowditch's
relative hyperbolicity of almost malnormal quasiconvex subgroups, and a
combination theorem for the double). Unreviewed.

"Sofic action" is Gao--Kunnawalkam Elayavalli--Patchell Definition 2.1(5)
(`research/artifacts/gkp-2401-04945-verified.md`).

## Theorem A

Let `G` be word-hyperbolic and `H <= G` a subgroup that is

- quasiconvex,
- almost malnormal (`gHg^(-1) ∩ H` finite for every `g ∉ H`), and
- residually finite.

Suppose every word-hyperbolic group is sofic. Then the coset action
`G ↷ G/H` is sofic.

More precisely, without any soficity assumption: for every `R` there is a
finite-index normal subgroup `N_R ⊴ H` such that `Gbar_R = G/<<N_R>>` is
word-hyperbolic, `Hbar_R = H/N_R` is finite and injects into `Gbar_R`, and
the quotient map `pi_R` satisfies, on the ball `B_R` of `G`,

1. `pi_R` is injective on `B_R`;
2. for `g in B_R`: `pi_R(g) in Hbar_R` if and only if `g in H`.

So the marked pairs `(ker pi_R, pi_R^(-1)(Hbar_R))` converge to `({1}, H)`,
and if all the `Gbar_R` are sofic then `G ↷ G/H` is sofic.

Residual finiteness of `H` is automatic when `G` is linear (Malcev), e.g. for
cocompact lattices in `Sp(n,1)` or in `SO(n,1)`. It is also automatic for
`H = E(g)`, the maximal elementary subgroup of an infinite-order element,
which is always almost malnormal and quasiconvex. So Theorem A covers
amenable stabilizers, the case GKP could not settle.

## Corollaries

**B (the flagship as an action problem).** If some hyperbolic group `G` has
an almost malnormal quasiconvex residually finite subgroup `H` with
`G ↷ G/H` not sofic, then some hyperbolic quotient `Gbar_R` of `G` is not
sofic. Conversely a nonsofic hyperbolic `G` gives such a pair with `H = {1}`.
So the flagship is equivalent to the existence of a nonsofic almost malnormal
quasiconvex coset action of a hyperbolic group. The gain is in the forward
direction: `G` may be taken sofic, even linear, and then the certificate is a
property of an action, not of the group.

**C (wreath and double certificates funnel into the flagship).** If every
hyperbolic group is sofic, then for every pair as in Theorem A and every
sofic `K` the generalized wreath product `K wr_(G/H) G` is sofic (GKP
Theorem 3.6), `M wr_(G/H) G` is Connes-embeddable for every Connes-embeddable
`M` (GKP Theorem 3.8), and the double `G *_H G` is sofic
(`sofic-coset-action-makes-amalgam-double-sofic`). So a **non-hyperlinear**
generalized wreath product `K wr_(G/H) G` with `K` hyperlinear and `(G,H)` as
in Theorem A would already produce a nonsofic hyperbolic group.

**D (what a certificate must look like).** In a certificate pair `(G,H)`:

- `H` is not separable in `G`
  (`sofic-coset-actions-pass-to-marked-colimits`, item 1);
- so `G` is not virtually compact special, because there quasiconvex
  subgroups are separable (Haglund--Wise);
- a Kun--Thom-type stabilizer is excluded: the infranormal pairs of
  `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup` are not
  quasiconvex. An infinite almost malnormal `H` is its own commensurator,
  so a stabilizer normalized or centralized by an element outside it, as in
  the compression and commuting-pair constructions of
  `hyperbolic-local-embedding-kills-compression-certificates`, is excluded.

The natural hosts are cocompact lattices in `Sp(n,1)`: Kazhdan, linear,
not virtually special, with no known separability of quasiconvex subgroups.

## Paradigm answers

- **Why this can succeed where the group-level certificates died.** The
  predecessor kills (compression defects, commuting pairs) are statements
  about the group. Nonsofic set actions are known to exist
  (`coordinate-action-not-sofic`), and GKP could not settle even amenable
  stabilizers. Theorem A is the first bridge that carries a nonsofic ACTION
  of a possibly sofic group into a nonsofic hyperbolic group.
- **First falsifiable step.** Take a cocompact `Sp(n,1)` lattice `Lambda`
  and an infinite-order `g`, and decide soficity of the amenable-stabilizer
  action `Lambda ↷ Lambda/E(g)`. Theorem A applies, since `E(g)` is almost
  malnormal, quasiconvex and virtually cyclic. The case lies inside the gap
  GKP left open (amenable stabilizers). A proof that every almost malnormal
  quasiconvex coset action of a sofic hyperbolic group is sofic would kill
  this certificate class.
- **Calibration.**
  - Free groups: all actions are sofic (GKP Theorem 2.19), matching the
    conclusion.
  - Virtually special hosts: the pair is LEF, so the action is sofic.
  - The residual-finiteness analogue is
    `relative-nonrf-target-iff-hyperbolic-nonrf`.
  - The Kun--Thom nonsofic action is not almost malnormal and quasiconvex in
    a hyperbolic host. So the theorem does not "prove" a nonsofic hyperbolic
    group from known data, which it could not.

DERIVATION
malnormal-coset-action-soficity-from-hyperbolic-fillings-proof
