---
rg: 2
id: fpbs-locally-free-free-actions-have-finite-cost
kind: claim
title: Every free action of a countable locally free group with finite c* has finite cost
distinct_from:
  fpbs-locally-free-free-action-costs-are-c-star-or-infinite: that is the established dichotomy C(a) in {c*, infinity}; this is the open statement that the value infinity never occurs when c* is finite.
  fpbs-fixed-price-non-amenably-generated-from-fg: that is conditional on fixed price for finitely generated groups and concerns a different class; this is unconditional and only for locally free groups.
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

**OPEN.** Let `Γ` be a countably infinite locally free group with
`c*(Γ) < ∞`, where `c*` is as in
`locally-free-groups-first-l2-betti-equals-c-star-minus-one`. Prove that every
free p.m.p. action of `Γ` has finite cost.

**Why it matters.** By `fpbs-locally-free-free-action-costs-are-c-star-or-infinite`,
this statement gives fixed price `c* = 1 + beta_1^(2)(Γ)` for every such `Γ`.
Groups with `c* = ∞` have fixed price ∞. The route
`fpbs-locally-free-fixed-price-from-finite-cost` records this.

**How it can fail.** A counterexample is a locally free `Γ` with `c* < ∞` and
a free action `b` of infinite cost. Then:
- `E_b` is an increasing union of subgroup orbit relations of cost at most
  `c*`, with infinite total cost;
- it answers Tucker-Drob Q 7.6 positively;
- `E_b` is not treeable, by Tucker-Drob Cor 6.8(2).

If some other free action of the same `Γ` has finite cost, `Γ` refutes fixed
price.

**First test.** `Γ_mal = lim(F_2 → F_2 → ⋯)` along `a ↦ a`, `b ↦ bab⁻²`, with
`c* = 2`. Does every free action of `Γ_mal` have cost 2?

## Attempts

**Anchors and weak containment (September 17, 2026; artifact §6).** These
routes give nothing new:
- **Proposition F anchors.** A locally free group that is neither finitely
  generated nor locally cyclic has no infinite finitely generated normal
  subgroup. This follows from Karrass–Solitar and Schreier's formula.
- **Weak containment.** Cost monotonicity under weak containment is imported
  only for finitely generated groups. For arbitrary groups only pseudocost is
  monotone, and pseudocost is already pinned to at most `c*`.

**Malnormal-hull dichotomy (September 17, 2026; worker
swarm-0917-w4-fp-lf-finite-cost).** Route
`fpbs-locally-free-finite-cost-by-hull-dichotomy` splits this hole into two
prerequisites.
- **Established half.** `fpbs-wq-normal-subgroup-cost-transfer`: for any
  countable group, free action `a` and infinite `H`, `C(a|W(H)) <= C(a|H)`
  (the price-one absorption induction, started from a near-optimal graphing of
  `R_H`). Hence `fpbs-locally-free-wq-normal-fg-subgroup-fixed-price`: the
  malnormal hull of every finitely generated subgroup of a locally free group
  has fixed price at most its rank, and if some finitely generated subgroup has
  hull `Gamma`, then `Gamma` has fixed price `c*`.
- **Open half.** `fpbs-locally-free-malnormally-exhausted-finite-cost`: groups
  with no finitely generated wq-normal subgroup, which are strictly increasing
  unions of proper malnormal subgroups of fixed price at most `c*`. `Gamma_mal`
  is here. Both known repair tools (wq-normal absorption and infinite-contact
  repair) provably stop at every finitely generated anchor in this class.
- **Where the direct attack stops.** Adding one stage generator of `Gamma_mal`
  on a sparse set needs absorption certificates; only 3 two-letter and about
  10 three-letter certificates exist (`experiments/locally-free-finite-cost-2026-09-17/`),
  so no short redundancy forces absorption, while certificate counting gives no
  lower bound on relative cost either.

**Measured absorption with arbitrary labels (September 17, 2026; worker
swarm-0917-w5-fp-lf-finite-cost).** This asks whether zero-cost absorption by
measurable partial isomorphisms can beat the group-element cap `W(H)`. It
cannot. See `fpbs-malnormal-measured-absorption-cap` and
`research/artifacts/fpbs-measured-absorption-cap-2026-09-17.md`.
- **Theorem A.** For any Borel `S ⊆ E_{a|Lambda}` and any `phi ∈ [[E_a]]` with
  label `gamma`, `gamma(x) ∈ Q(Lambda)` almost everywhere where `phi(S) ∩ S`
  has infinite classes. The proof uses the coset cocycle
  `c(x) = Lambda gamma(x)`, whose fibres meet a class in at most
  `|Lambda ∩ gamma^{-1} Lambda gamma|` points.
- **Cap.** Transfinite infinite-contact chains from `E_{a|H}` stop exactly at
  `E_{a|W(H)}`. Normalizers, quasi-normalizers and window-trick maps of
  `E_{a|M}`, for almost malnormal `M`, lie in `[[E_{a|M}]]`.
- **Where it dies.** In the malnormally exhausted class every finitely
  generated anchor has a proper hull. Zero-cost absorption of any kind cannot
  leave a stage. Since `C(a) < ∞` iff `relC(E_a | E_{a|H_n}) -> 0`, a proof must
  pay for finite-contact partial maps with total mass tending to 0.
- **Still open.**
  - mixed chains (pay a sparse finite-contact map, then absorb from the new,
    non-subgroup relation);
  - contact-free percolation repairs;
  - a positive lower bound for `relC(E_{F_2} | E_{<a, bab^{-2}>})`.
