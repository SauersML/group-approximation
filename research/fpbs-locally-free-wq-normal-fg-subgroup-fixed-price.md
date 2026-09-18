---
rg: 2
id: fpbs-locally-free-wq-normal-fg-subgroup-fixed-price
kind: claim
title: A locally free group with a finitely generated wq-normal subgroup has fixed price c*, and so does the malnormal hull of every finitely generated subgroup
distinct_from:
  fpbs-locally-free-groups-have-fixed-price: that is the open statement for every locally free group; this settles the part where some finitely generated subgroup has malnormal hull equal to the group, and leaves exactly the malnormally exhausted groups.
  fpbs-locally-free-free-actions-have-finite-cost: that is the open finite-cost hole for all locally free groups; this proves it under the hull hypothesis.
---

**ESTABLISHED** through `fpbs-locally-free-wq-normal-fg-subgroup-fixed-price-proof`.

Let `Gamma` be a countably infinite locally free group and `c* = c*(Gamma)` as in
`locally-free-groups-first-l2-betti-equals-c-star-minus-one`.

1. **Hulls have fixed price.** For every nontrivial finitely generated
   `H <= Gamma`, its malnormal hull `W(H)` (the smallest malnormal subgroup
   containing `H`; for torsion-free groups almost malnormal means malnormal)
   has fixed price `c*(W(H)) = 1 + beta_1^(2)(W(H)) <= rk H`.
2. **Case (W).** If some finitely generated `H <= Gamma` has `W(H) = Gamma`
   (that is, `H` is wq-normal in `Gamma`), then every free p.m.p. action of
   `Gamma` has cost `c* <= rk H`. So `Gamma` has fixed price `c*`, and
   `fpbs-locally-free-free-actions-have-finite-cost` holds for `Gamma`.
3. **Dichotomy.** Otherwise `Gamma` is **malnormally exhausted**: it is the
   increasing union of the proper malnormal subgroups `M_n = W(Delta_n)`, where
   `(Delta_n)` is the compressed exhaustion of the artifact
   `research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md`
   (Lemma 2.1, `rk Delta_n <= c*`). Each `M_n` has fixed price at most `c*` by
   item 1, and the chain `(M_n)` does not stabilize, since a stable value would
   be a proper subgroup equal to `Gamma`. The remaining
   case is the OPEN claim `fpbs-locally-free-malnormally-exhausted-finite-cost`.

**A checkable criterion for case (W).** Suppose `Gamma = ∪_n Delta_n` with
`Delta_0 != 1` finitely generated and, for each `n`, a generating set of
`Delta_(n+1)` all of whose elements `g` satisfy `Delta_n ∩ g Delta_n g^(-1) != 1`.
Then `W(Delta_0) = Gamma`: by induction `Delta_n <= W(Delta_0)`, and a malnormal
subgroup containing `Delta_n` contains every such `g`. Sanity check: the limit
along `a -> a^2, b -> b^2` (which is `Z[1/2] * Z[1/2]`, already of fixed price 2
by Gaboriau's free product formula) is in case (W). `Gamma_mal` (limit along
`a -> a`, `b -> bab^{-2}`) is malnormally exhausted: its stages are malnormal
(`fpbs-malnormal-subgroup-relations-finite-contacts`, item 5, Stallings-graph
certificate).
