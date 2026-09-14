---
rg: 2
id: injective-ca-random-order-transport-identity
kind: claim
title: Decoder information transport under an i.i.d. random order sums to log |A| at every output site of an injective automaton
distinct_from:
  decoder-window-fiber-bound-loses-exactly-the-boundary: that is a per-window counting bound that loses the right boundary factor on nonamenable groups; this is an exact mass-transport identity over every group, with no windows and no loss.
  measure-conjugacy-invariants-cannot-certify-surjectivity: that rules out isomorphism invariants of the image action; this is an identity between functionals of the joint coordinate processes, which are not such invariants.
artifacts:
  - research/artifacts/random-order-decoder-transport-2026-09-12.md
---
**ESTABLISHED** (artifact Section 1, route `injective-ca-random-order-transport-identity-proof`).

Let `kappa : A^G -> B^G` be injective, `y = kappa(x)` with `x` uniform, `N` the memory of a left inverse with
`e in N`, and `U` i.i.d. uniform labels independent of `x` defining a random order `≺`. Then

    sum_(n in N) I( x(n^-1) ; y(e) | y(n^-1 N ∩ past(e)), U ) = log |A| .

The input side is the chain rule over `N`, using that `x(e)` is a function of `y(N)`. The output side is the same
sum moved by left translation, which is the mass-transport principle for a countable group.

**Calibration** (artifact 2.1). On the end-fixing tree the same transport sends `log |A|` out of each vertex and
`(1/2) log |A|` in, so the identity uses that the index set is a group.
