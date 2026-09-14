---
rg: 2
id: fpbs-normal-subgroup-bounded-cost-fixed-price-one
kind: claim
title: An infinite normal subgroup of infinite index with uniformly bounded action cost forces fixed price one
distinct_from:
  fpbs-factor-invariance-equals-fixed-price: that is the general equivalence between fixed price and cost invariance under free factor maps for a fixed group; this is a specific sufficient structural condition, an infinite normal subgroup of infinite index whose free actions have bounded cost, asserted to give fixed price one.
  fpbs-burnside-upper-cost-one: that is the numerical assertion c_n=1 for large odd Burnside groups; this is a general statement about group extensions, which would imply that assertion through the route fpbs-burnside-upper-cost-one-via-normal-closure but is not implied by it.
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

**OPEN.** Let `N` be an infinite normal subgroup of a countable group `Gamma`
with `Gamma/N` infinite. Suppose there is `K < infinity` such that every
essentially free p.m.p. action of `N`, ergodic or not, has cost at most `K`.
Then every essentially free p.m.p. action of `Gamma` has cost one, i.e.
`Gamma` has fixed price one.

This is the fixed price version of Gaboriau's normal subgroup theorem, which
gives only infimal cost one (Donoso-Echenique--Silva, arXiv:2608.20472,
Theorem 2.2). The hypothesis holds with `K = d(N)` for finitely generated
`N`, and with `K = 2` for every infinite subgroup of a large odd free Burnside
group by `fpbs-burnside-common-upper-cost`.

**Known cases.** Direct products of two infinite countable groups have fixed
price one with no cost hypothesis (Khezeli, arXiv:2509.08325, Theorem 1.1).
Bevilacqua--Bowen, arXiv:2510.05459, state that `Gamma x Gamma` was previously
known only when `Gamma` has an infinite amenable subgroup, so the statement is
not classical even for finitely generated `N` with a commuting complement.
Infinite amenable `N` is covered by Gaboriau's weakly normal criterion.
`fpbs-quotient-split-actions-have-cost-one` proves the conclusion for every
action that factors onto a free finite-cost action of `Gamma/N`.

**Consequence.** With `fpbs-burnside-normal-closure-split` and
`fpbs-burnside-common-upper-cost` this gives `c_n = 1`, i.e.
`fpbs-burnside-upper-cost-one`, through
`fpbs-burnside-upper-cost-one-via-normal-closure`. That would close the
Burnside counterexample branch `fpbs-burnside-positive-upper-cost` in the
negative direction.

## Attempts

* **Theorem A plus weak containment.** Section 1 of the linked note proves
  cost one for quotient-split actions: select a sparse set of whole `N`-orbits
  as the preimage of a small complete section of the quotient action, use the
  bounded `N`-cost only there, attach every other point by one edge, and
  connect the selected orbits through a fibrewise-sparse complete section.
  The natural upgrade exhibits such an action weakly contained in the
  Bernoulli shift, so that monotonicity of cost under weak containment and
  Abert--Weiss maximality give fixed price one. **Dead for nonamenable `N`:**
  `fpbs-quotient-split-not-bernoulli-contained` shows no action with a
  nontrivial `N`-invariant factor is weakly contained in the Bernoulli shift.
  That kills `fpbs-dead-split-cost-one-weak-containment-transfer`.
* **Select `N`-orbits inside an arbitrary action.** Theorem A needs an
  `N`-invariant set of small positive measure meeting every orbit. **Where it
  dies:** no such set exists when the restriction to `N` is ergodic, which is
  already the case for the Bernoulli shift of `Gamma`. This is the
  vertical-constancy obstacle that Khezeli's proof for products avoids with
  horoball processes built as weak limits of factors of i.i.d.
* **Adapt Khezeli's horoballs to extensions.** Deferred. That construction
  uses a left-invariant weighted product metric and two commuting infinite
  directions. In a split extension `N semidirect H` the complement does not
  commute with `N`; no analogue is constructed here.
* **Restate as factor invariance.** Under the hypothesis, the statement is
  equivalent, through `fpbs-factor-invariance-equals-fixed-price` and Theorem
  A, to cost preservation along `alpha x sigma -> alpha` for free actions
  `alpha` of `Gamma` and free finite-cost actions `sigma` of `Gamma/N`. This
  is a restatement, not a reduction, so it is not recorded as a route.
