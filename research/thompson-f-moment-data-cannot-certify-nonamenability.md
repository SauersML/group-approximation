---
rg: 2
id: thompson-f-moment-data-cannot-certify-nonamenability
kind: claim
title: Finitely many exact closed-walk counts on Thompson's group F never certify non-amenability
distinct_from:
  thompson-f-random-walks-are-not-liouville: that is about nonconstant bounded harmonic functions for random walks on F; this is about what finitely many return probabilities of simple random walk can and cannot prove about the norm of the Markov operator.
  thompson-f-folner-function-exceeds-every-tower: that is a lower bound on the Følner function; this is a statement about truncated moment data of the spectral measure.
---

**ESTABLISHED.** Let `P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`, and let
`mu` be its spectral measure at `delta_e`. Its odd moments vanish and its even moments are
`M_j = c_{2j} / 16^j`, where `c_{2j}` counts words of length `2j` in `x_0^{+-1}, x_1^{+-1}`
that are trivial in `F`.

For every `N` there is a symmetric probability measure `nu` on `[-1, 1]` with the same even
moments `M_0, ..., M_N` and with `+-1` in its support.

**Consequence.** No finite list of exact counts `c_0, ..., c_{2N}` implies `||P|| < 1`.
By Kesten's criterion `||P|| < 1` is equivalent to non-amenability of `F`, so certified
cogrowth computations can only give lower bounds on `||P||`, never a proof of
non-amenability. A proof has to use infinitely many counts or structure beyond the moments.

**Scope.**
- The argument uses only that the spectrum of `P` is infinite. It applies to every
  symmetric random walk on a torsion-free group whose complex group ring has no nontrivial
  idempotents.
- It says nothing about which way the amenability question goes.
- Novelty is not claimed. The moment-space facts are classical (Krein–Nudelman); what is
  recorded here is the application to `F`.

Proof route: `thompson-f-moment-barrier-proof`.
