---
rg: 2
id: f-dyadic-ea-iff-inverted-orbit-confinement-proof
kind: route
title: Specialize the inverted-orbit reformulation of extensive amenability to the transitive finitely generated action of F on the dyadic rationals
target: f-dyadic-ea-iff-inverted-orbit-confinement
requires: []
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

**Source.** K. Juschenko, N. Matte Bon, N. Monod, M. de la Salle, *Extensive amenability and an
application to interval exchanges*, arXiv:1503.04977 (ETDS 38 (2018) 195–219). The arXiv source
(`extAmen2.tex`) was fetched and read on 2026-09-14.

**Verbatim (Proposition, §"The inverted orbit").** "Fix `G ↷ X`, `x_0 ∈ X` and `μ` as before. The
following properties are all equivalent to extensive amenability.
(i) `lim_{n→∞} −(1/n) log E(2^{−|O_n|}) = 0`.
(ii) for every `ε > 0` we have `P(|O_n| < ε n) > e^{−ε n}` for infinitely many `n`'s.
(iii) There exists a sequence of events `A_n ∈ σ(g_1,…,g_n)` verifying `−(1/n) log P(A_n) → 0`, conditioned
to which `(1/n) E(|O_n| : A_n) → 0`. In particular these conditions do not depend on `μ` and `x_0`."

The proposition's hypotheses ("as before"): `G = ⟨S⟩` finitely generated acting transitively on `X`, `μ`
symmetric with generating support, base point `x_0`, and `O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0}` the inverted
orbit of the left random walk.

**Verification of the hypotheses for `F ↷ D`.**
- `F = ⟨x_0, x_1⟩` is finitely generated.
- `F` acts transitively on `D ⊂ (0,1)`: any two dyadics `s, t` are the images `.u` and `.v` of a common
  leaf under two standard subdivisions of `[0,1)` with equally many leaves, and the tree-pair element
  sending the first subdivision to the second maps `s` to `t` (recorded in
  `jones-subgroup-coamenable-from-extensive-amenability-proof`, step 1).

So the proposition applies verbatim with `G = F`, `X = D`. This gives the equivalence of items 1, 2 and 3
of the claim.

**Item 4 (return probability of the switch-walk-switch walk).** In the proof of the proposition the authors
use, from Juschenko–Monod, that `F ↷ D` is extensively amenable iff `(Z/2)^{(D)} ⋊ F ↷ (Z/2)^{(D)}` is
amenable, and then, with `ν` the switch-walk-switch measure `λ ∗ μ ∗ λ` (`λ` uniform on
`{0, δ_{x_0}}`), that the induced walk `f_n` on the trivial-configuration Schreier graph satisfies
`P(f_n = f_0) = E(2^{−|O_n'|}) = E(2^{−|O_n|})` (each visited point is lit independently with probability
`1/2`, and `O_n, O_n'` are equal in law for fixed `n`). By Kesten's amenability criterion for graphs
(Woess, Thm 10.6, as cited there) amenability of that action is `−(1/n) log P(f_n = f_0) → 0`. Combined
with item 2 this is item 4.

**No novelty.** This is a direct instantiation of a published equivalence; the only added content is
checking transitivity of `F ↷ D`. The statement's value is that it fixes the concrete target for the open
node `thompson-f-dyadic-action-is-extensively-amenable`.
