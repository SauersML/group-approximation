---
rg: 2
id: fournier-facio-asymptotic-triviality-from-normal-kazhdan-defect
kind: route
title: Full defect saturation makes every asymptotic representation trivial
target: fournier-facio-asymptotic-representations-trivial
requires: [normal-kazhdan-defect-non-mf, fournier-facio-torsion-free-skeleton, defect-normally-generates-torsion-free-quotient]
artifacts:
  - research/artifacts/router-detector-torsion-free-non-mf-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
---

## Proof

Let `phi_n : G -> U(k_n)` be an operator-norm asymptotic homomorphism and set

`Q = (prod_n M_{k_n}(C)) / (oplus_n M_{k_n}(C))`,

where the ideal consists of norm-null sequences.  The classes

`Theta(g) = [(phi_n(g))]`

form an exact group homomorphism `Theta : G -> U(Q)`: the multiplicative
defect is norm-null by hypothesis, hence vanishes in the quotient.

Let `K = <<pi(S)>>^G`.  The established claim
`defect-normally-generates-torsion-free-quotient` gives the strongest form
`K = G`; in the same construction `K` lies in the compression defect and is
Kazhdan.  The established machine-checked killing theorem
`normal-kazhdan-defect-non-mf` therefore says that every homomorphism from
`G` to a norm matrix corona kills `K` elementwise.  Since `K = G`, `Theta`
is the trivial homomorphism.

For every fixed `g`, `Theta(g) = 1` means precisely that
`(phi_n(g) - 1)_n` lies in the norm-null ideal.  Thus

`||phi_n(g) - 1|| -> 0`.

This proves the claim.  Notice that the conclusion is strictly stronger
than matricial stability: no search for correcting representations is
needed; the constant trivial representation is always a correction.

## The machine-checked step, named

The killing step is
`KazhdanCompressionCore.normalKazhdan_le_normMatrixCStarCoronaKernel`
(`Sofic/NormalKazhdanMFRadical.lean`): for a countable `E`, a normal `K` with
`HasKazhdanPropertyT K` and `K <= C.defectNormal`, **every**
`rho : E ->* unitary (NormMatrixCStarCorona X)` satisfies `K <= rho.ker`.
Applied at `K = G` — legitimate because the established form of
`defect-normally-generates-torsion-free-quotient` gives
`C.defectNormal = <<pi(S)>>^G = G`, so no inheritance of property (T) is
needed — it gives `G <= Theta.ker` directly.

Two definitional details the argument leans on, both discharged in the
repository rather than assumed here.  `NormMatrixCStarCorona X` is the corona
along the **cofinite** filter, so `[u_n] = 1` unwinds to the ordinary limit
`||u_n - 1|| -> 0` rather than to an ultrafilter limit.  And `phi_n(1)` need
not equal `1`: a unitary with `phi_n(1)^2 - phi_n(1) -> 0` has
`phi_n(1) -> 1`, which is what makes `Theta` unital and hence a homomorphism
into the unitary group rather than merely a multiplicative map.
