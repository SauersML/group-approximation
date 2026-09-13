---
rg: 2
id: simple-group-relator-templates-over-finite-simple-groups
kind: claim
title: A finitely presented simple group not linear sofic over finite fields has one relator template valid over all finite simple groups, so bounded width over all their direct products
distinct_from:
  simple-group-width-over-all-finite-simple-groups: that bounds the number of relator conjugates over each finite simple group separately, with a pattern depending on the tuple; this fixes one word pattern for all finite simple groups and all tuples, which is what passes to direct products with unboundedly many factors.
  relator-width-over-nilpotent-by-locally-finite-groups: that produces one template over nilpotent-by-(locally finite variety) groups without soficity hypotheses; this produces one template over the finite simple groups of unbounded order under non-linear-soficity over finite fields.
  simple-nonsofic-relator-width-over-iterated-wreath-products: that is the open depth-uniform bound over iterated wreath products and records that templates pass to direct products; this supplies templates for simple vertex groups of unbounded order.
---

**ESTABLISHED (unreviewed).** Let `G = <X | R>` be an infinite finitely presented simple group that is
not linear sofic over finite fields (`simple-group-psl-width-is-finite-field-linear-soficity`).

**Definitions.**
- A *template* for `x in X` is a formal product `omega = prod_(i<=L) (r_i^(eps_i))^*` with `r_i in R`
  and `eps_i = +-1`.
- An *evaluation* of `omega` at `(Q, a)` is `prod_i g_i r_i(a)^(eps_i) g_i^-1` with any `g_i in Q`.
- `omega` is *valid* over a class of groups if, for every `Q` in the class and every `a in Q^X`,
  `a_x` is an evaluation of `omega`.

**Theorem.** There are templates `omega_x` (`x in X`) valid over the class `S` consisting of:
- all finite simple groups, abelian ones included;
- the quasisimple groups `SL_n(q)/Z_0`, `Sp_n(q)/Z_0`, `SU_n(q)/Z_0` and `Omega^+-_n(q)/Z_0`, whose central
  quotient is simple.

**Corollary (semisimple targets).** A template valid over a class is valid over all finite direct
products of its members, with conjugators chosen coordinatewise. So there is `K = K(G)` with
`w_Q(a) <= K` for every direct product `Q = Q_1 x ... x Q_k` of members of `S`, with `k` arbitrary.
No sequence of weak models of `G` with bi-invariant lengths has direct products of finite simple groups
as targets.

**Consequence for `fg-simple-weakly-sofic-groups-are-sofic`.** For finitely presented `G` not linear sofic
over finite fields, targets of weak models must eventually be neither nilpotent-by-(bounded type)
(`relator-width-over-nilpotent-by-locally-finite-groups`) nor semisimple direct products. What remains
are twisted products, where a large top acts on many simple or nilpotent layers: wreath-type groups
(`simple-nonsofic-width-over-bounded-base-symmetric-wreath`,
`simple-nonsofic-relator-width-over-iterated-wreath-products`), and nilpotent kernels under large simple
tops. Examples of the latter are congruence and affine groups `F_q^n ⋊ SL_n(q)` with `n` unbounded.

**Mechanism.** `omega_x = prod_(j<=J) (B^N (B^N)^*) · n_x`, where:
- `B = prod_(r in R) (r, r^-1)`, and `^*` reverses the word and inverts the signs;
- `x = prod_j [c_j, c'_j] n_x` is the double-commutator template of `G = G''`.

Every pair `(r, r^-1)` can evaluate to `1`, to any conjugate of a seed `[r(a), y]`, or, when `r(a)`
normalizes a subgroup `H`, to anything in `C C^-1`, with `C` the `H`-orbit of `r(a)`. So each family's
covering proof, which uses one seed family and Liebeck--Shalev in a subgroup `H`, runs with a fixed power
`B^N`. Unused pairs evaluate to `1`.

Derivation: `simple-group-relator-templates-over-finite-simple-groups-proof`.
