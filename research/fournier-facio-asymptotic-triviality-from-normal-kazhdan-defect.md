---
rg: 2
id: fournier-facio-asymptotic-triviality-from-normal-kazhdan-defect
kind: route
title: Full defect saturation makes every asymptotic representation trivial
target: fournier-facio-asymptotic-representations-trivial
requires: [normal-kazhdan-defect-non-mf, fournier-facio-torsion-free-skeleton, defect-normally-generates-torsion-free-quotient]
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
