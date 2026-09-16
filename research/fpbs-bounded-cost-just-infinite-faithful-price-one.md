---
rg: 2
id: fpbs-bounded-cost-just-infinite-faithful-price-one
kind: claim
title: A bounded-cost normal subgroup with finite center and a faithful just-infinite finitely generated torsion outer quotient forces fixed price one
distinct_from:
  fpbs-bounded-cost-fg-torsion-quotient-price-one: that allows any infinite finitely generated torsion quotient and an outer kernel with no infinite amenable subgroup; this is its special case with a just-infinite quotient, a faithful outer action and finite center, and the two are equivalent through fpbs-bounded-cost-fg-torsion-via-just-infinite-reduction.
  fpbs-bounded-cost-locally-finite-outer-price-one: that is the locally finite quotient case; this quotient is finitely generated and infinite, hence not locally finite.
  fpbs-infinite-centralizer-forces-price-one: that settles every infinite centralizer with no cost bound; this assumes the centralizer is finite, so that lemma does not decide it, and the cost bound must be used.
artifacts:
  - research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md
---

**Statement.** Let `N` be an infinite normal subgroup of a countable group
`Gamma`. Suppose every essentially free p.m.p. action of `N` has cost at most
some `K < infinity`. Suppose `Q = Gamma/N` is infinite, finitely generated,
torsion and just-infinite. Suppose also that `C_Gamma(N)` is finite and
contained in `N`. Then `Gamma` has fixed price one.

**Equivalent forms of the last hypothesis.** `C_Gamma(N) ⊆ N` and finite
means exactly two things:
- the outer action `Q -> Out(N)` is faithful;
- the center `Z(N)` is finite.

**Status of the reduction.** By
`fpbs-bounded-cost-fg-torsion-via-just-infinite-reduction` this statement
implies `fpbs-bounded-cost-fg-torsion-quotient-price-one`. It even implies
that statement without its outer-kernel hypothesis. Conversely it is a special
case of that statement.

**Burnside.** Take the split `B(m,n) = N ⋊ B(m-1,n)` with `m >= 3`. Enlarging
`N` by the preimage of a maximal infinite-index normal subgroup of the quotient
gives an instance: the centralizer of the enlarged subgroup lies in the finite
cyclic centralizer of `x_1`, so step 4 of the reduction route applies. So this statement, with the other premises of
`fpbs-burnside-upper-cost-one-via-fg-torsion-quotient`, implies fixed price one
for large odd free Burnside groups.

## Attempts

* **Infinite centralizer or infinite outer kernel.**
  - `fpbs-infinite-centralizer-forces-price-one` settles these with no cost
    bound.
  - **Where it dies:** here `C_Gamma(N)` is finite by hypothesis. No
    commuting pair of infinite normal subgroups exists: if `M ◁ Gamma` commutes
    with `N`, then `M ⊆ C_Gamma(N)` is finite. Pairs that commute modulo a
    finite normal subgroup are also removed, by Corollary C.2 of the linked
    artifact, so a proof may assume none exist.
* **Enlarging the normal subgroup.**
  - Every `N ⊆ Lambda ◁ Gamma` inherits the cost bound by Lemma B of the
    linked artifact.
  - Fixed price one lifts from `Lambda` by wq-normality.
  - **Where it dies:** just-infiniteness leaves only `Lambda = N` or
    `Lambda/N` of finite index in `Q`. The first is the hypothesis. In the
    second, `(Lambda, N)` is again an instance of the same problem, so nothing
    is gained.
* **Infinite locally finite subgroups of the quotient.**
  - Suppose `S <= Q` is infinite and locally finite, and put
    `Lambda = pi^-1(S)`.
  - Then `N ◁ Lambda` still satisfies the cost bound, `Lambda/N ≅ S`, and the
    outer action of `S` on `N` is faithful. So `(Lambda, N)` is an instance of
    `fpbs-bounded-cost-locally-finite-outer-price-one`.
  - Fixed price one for `Lambda` would lift to `Gamma`, since `Lambda ⊇ N` is
    wq-normal.
  - **Where it dies:** that claim is open. It is also unknown whether the
    just-infinite quotients arising from `B(m-1,n)` contain an infinite
    locally finite subgroup. `B(m-1,n)` itself has none, because for large odd
    `n` its finite subgroups are cyclic. That last fact is recalled from the
    Adian and Ol'shanskii theory and was not fetched.
* **Quotient-split actions.** Theorem A of
  `fpbs-quotient-split-actions-have-cost-one` gives cost one when the action
  has a free finite-cost factor of `Q`.
  - **Where it dies:** Bernoulli shifts of `Gamma` have no such factor, and the
    weak containment upgrade is dead by
    `fpbs-quotient-split-not-bernoulli-contained`.
* **Cheap graphings of the fibres.**
  - The normal criterion only gives `C(R_Gamma) <= C(R_N) <= K`.
  - **Where it dies:** it gives nothing below `K`. A proof must exploit how
    the quotient permutes the `R_N`-classes. When the quotient is torsion with
    no infinite-order element, there is no Rokhlin tower in the quotient
    direction to exploit.
