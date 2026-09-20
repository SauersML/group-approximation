---
rg: 2
id: low-energy-povms-round-equivariantly-in-place-proof
kind: route
title: "Liu's all-label invariant range construction rounds POVMs in place"
target: low-energy-povms-round-equivariantly-in-place
requires: []
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
---

## Attribution and proof

This is an independently verified exposition of **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 4.3, not a new result or proof mechanism of Cairn.
Section B of the acceptance artifact gives the complete proof. Its two
identified standard finite-algebra imports are Houdayer–Vaes,
[*Type III factors with unique Cartan decomposition*, Lemma 2.1](https://arxiv.org/pdf/1203.1254),
and Ioana, [*Almost commuting matrices and stability for product groups*,
Lemma 2.2(1)](https://ems.press/content/serial-article-files/47873).

Coarea cuts of the effects give projections f_i with vanishing summed
energy, S=sum f_i<=3I, squared cut distance at most 2v, and
||S-I||_2^2<=12v. Their column W lives in an auxiliary space of dimension
at most 4d, always with trace denominator d. Polar-completed auxiliary
generators make W invariant in the ultraproduct. In that abstract finite
commutant, the credited comparison and near-identity conjugacy lemmas
move its range to a projection commuting with the entire internal
scalar-label algebra, at squared distance cost at most 400v.

The all-label phase-average identity lifts this one range projection
label-diagonally: any nonvanishing pinching defect would admit a bounded
coordinate phase witness contradicting its commutation with the label
algebra. Delete only the asymptotically negligible rank excess above d,
then lift the partial isometry by singular values. The resulting label
projections pull back to an orthogonal family in the original M_d; add
its invariant remainder to one outcome.

Orthogonality bounds all energy errors in one Hilbert direct sum, with
no factor counting labels. The distance bound is
```
lim_omega sum_i ||q_i-a_i||_2^2
  <= (40+sqrt(12)+sqrt(2))^2 v <=5000v.
```
The output total energy tends to zero even when v is positive. A
counterexample sequence with input energy at most 1/n would violate
these two limits, proving the uniform finite delta(h,epsilon).

The auxiliary commutant and its MASA are not assumed internal, and no
MASA lift is used. The artifact checks the standard imports' hypotheses,
all rank corrections, and the variable-outcome sums. This is a complete
written proof with those explicit ordinary mathematical imports, not a
blanket paper import, a novelty claim, or a Lean certification.
