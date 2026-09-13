---
rg: 2
id: rainone-free-minimal-f2-action-not-almost-unperforated
kind: claim
title: Some free minimal action of F_2 on the Cantor set has a type semigroup that is not almost unperforated (Rainone's F_2 question)
distinct_from:
  rainone-non-almost-unperforated-minimal-outer-action-exists: that is Rainone's general question, answered for topologically free minimal actions of F_infinity by Boldrini--Prasad; this is his F_2 sub-question, with a free action.
  free-minimal-cantor-action-with-finite-clopen-type: that allows any countable group but demands no invariant measure and a finite clopen class; this asks for F_2 and only a failure of almost unperforation.
  free-minimal-fn-cantor-action-not-almost-unperforated: that allows any finite rank at least 2 and implies this by induction.
root: true
---

**Root (2026-09-13, ex3-rainone-f2-free).**  Rainone, *Finiteness and
paradoxical decompositions in C\*-dynamical systems*, arXiv:1502.06153v1,
p. 33 (J. Noncommut. Geom. 11 (2017)), verbatim: "In particular, is there a
free and action of the free group F_2 on the Cantor set X for which
S(X, F_2, C) is not almost unperforated? Although Ara and Exel construct
actions of a finitely generated free group on the Cantor set for which the
type semigroup is not almost unperforated, these actions are not minimal
[1]."  "A free and action" is Rainone's typo; the preceding sentence asks for
minimal properly outer actions, and the Ara--Exel remark shows that minimality
is the point.

**Statement (OPEN).**  There is a free minimal action of `F_2` on a Cantor
space `X` such that `S(X, F_2)` is not almost unperforated.

**Status.**  Boldrini--Prasad (arXiv:2607.01896v1, Theorems 6.1 and 6.10)
give minimal, *topologically free* actions of `F_infinity` without dynamical
comparison, which answers the general question in substance.  Their argument
does not give a free action or a finitely generated group.  The bounded
novelty pass (`research/artifacts/ex-novelty-rainone-p33-pass-2026-09-13.md`)
found no answer to this sub-question.  Any finite rank suffices:
`rainone-f2-question-via-finite-rank-free-subgroup`.

## Attempts

* **Generic pairs in `Aut(B, mu)^2`** (Boldrini--Prasad's Fraïssé algebra).
  * Exhaustive pairs are not dense: the pairs fixing a common nontrivial
    clopen form a nonempty open set with no exhaustive member (recorded on
    `free-minimal-cantor-action-with-finite-clopen-type`).
  * The set `Q` of pairs with no common invariant clopen is closed.  On
    finite data `(A, alpha, beta)`, some nontrivial element of `A` is
    invariant under both exactly when the overlap graph on atoms of `A`
    (`q -- q'` iff `alpha(q) ∧ q' != 0` or `beta(q) ∧ q' != 0`) is
    disconnected.  The join `p` of a component has `alpha(p) <= p` and
    `alpha(1 - p) <= 1 - p`, so `alpha(p) = p`.
  * Where it dies: routing a piece along a path of atoms needs an extension
    of `alpha` whose value on a chosen sub-piece lies in a prescribed overlap.
    That needs a refinement of `mu(x_0) + mu(q - x_0) = mu(y_0) + mu(alpha(q) - y_0)`
    with a nonzero corner, which is unproved for non-cancellative `M`.
    Density of exhaustiveness in `Q` is open, and freeness is a further step.
* **Profinite diagonal products** `X x lim F_2/N_j`.
  * The product action is free.  If every `N_j` still acts exhaustively, the
    type semigroup is the direct limit of `M` along multiplication by
    `[N_j : N_(j+1)]`.
  * Where it dies: every perforation witness dies in that limit.  From
    `(n+1)x <= ny`, every `m >= n^2` has some `k` with `kn <= m <= k(n+1)`,
    so `mx <= k(n+1)x <= kny <= my`.  This firewall is specific to that
    design, since restrictions need not stay exhaustive.
* **Cocycle skew products** `X x_c K`, `K` a profinite group.
  * The action is free when `c(gamma, x) != e` whenever `gamma x = x`,
    `gamma != e`.  Downstairs subequivalences lift, so the pullback of types
    preserves order.
  * A relation between pullbacks realized at a finite level of size `d`
    gives only `d x <= d y` downstairs.  So a perforation witness can survive
    only through rigidity of the cocycle.  Unexplored.
* **Ara--Exel separated-graph actions.**  Finitely generated free groups,
  types not almost unperforated, not minimal (Rainone's remark).  Minimality
  would need a simple type semigroup; unexplored here.
