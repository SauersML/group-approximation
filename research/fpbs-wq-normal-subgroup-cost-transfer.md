---
rg: 2
id: fpbs-wq-normal-subgroup-cost-transfer
kind: claim
title: A free action costs at most its restriction to any infinite wq-normal subgroup
distinct_from:
  fpbs-wq-normal-price-one-subgroup-forces-price-one: that is the price-one case, where the subgroup has fixed price one; this is the general per-action cost inequality C(a) <= C(a|H), for any value of C(a|H), by the same absorption induction.
  fpbs-wq-normal-hull-is-almost-malnormal: that is the group-theoretic hull; this is the measure-theoretic cost bound that uses it.
---

**ESTABLISHED** through `fpbs-wq-normal-subgroup-cost-transfer-proof`.

Let `Gamma` be a countable group, `H <= Gamma` an infinite subgroup with
wq-normal hull `W(H)` (as in `fpbs-wq-normal-hull-is-almost-malnormal`), and
`a` a free p.m.p. action of `Gamma`. Then

```text
C(a|W(H)) <= C(a|H).
```

In particular, if `H` is wq-normal in `Gamma` (equivalently `W(H) = Gamma`),
then `C(a) <= C(a|H)` for every free action `a`. If `H` is finitely generated
with `d` generators, every free action of `W(H)` has cost at most `d`.

Applied to locally free groups this gives
`fpbs-locally-free-wq-normal-fg-subgroup-fixed-price`.
