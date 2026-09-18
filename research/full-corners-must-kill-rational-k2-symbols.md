---
rg: 2
id: full-corners-must-kill-rational-k2-symbols
kind: claim
title: If E_N(R) is finitely presented and Q ⊆ R, then every full idempotent corner eRe sends K_2(Q) to a finite group
distinct_from:
  infinitely-generated-symbols-block-fp-elementary-groups: that bounds the symbols of commuting units of R itself; this applies it to the corner scalars λe + (1-e) and transports the bound into K_2(eRe), so that every corner, not only the unit, must kill almost all of K_2(Q).
  matricial-divisibility-kills-rational-k2-symbols: that is a sufficient condition for the unit corner; this is the necessary condition for every full corner, of which the matricially divisible corners are the known sufficient case.
  rational-k1-detection-forces-infinite-order-unit-class: that is the (K1) half, about the unit class in K_0; this is the (K2) half, about every idempotent class.
---

**ESTABLISHED** by `full-corners-must-kill-rational-k2-symbols-proof` (lane proof; inputs
are one landed lemma and two textbook facts, see the proof; not independently reviewed).

## Statement

Let `R` be a unital ring with a unital map `Q -> R`, let `N >= 3`, and suppose `E_N(R)` is
finitely presented. This holds, for instance, if `PE_N(R)` is finitely presented. Let `e ∈ R`
be a full idempotent (`ReR = R`; every nonzero idempotent is full when `R` is simple). Give
`eRe` the unital map `q ↦ qe`. Then the image of `K_2(Q) -> K_2(eRe)` is finite.

So every full corner of a host must kill all but finitely many of the tame symbols of
`K_2(Q) = (Z/4)^x ⊕ ⊕_(p odd) (Z/p)^x`.

## Consequences

- **The budget concerns every idempotent class, not only `[1]`.** For the premise
  `q-algebra-with-fp-simple-projective-elementary-group`, each nonzero corner `eRe` must kill
  almost all tame symbols. By `matricial-divisibility-kills-rational-k2-symbols` applied to
  `eRe`, it is sufficient that every nonzero corner be matricially divisible:
  `eRe ≅ M_n(S_n)` for `n` divisible by every integer. That is the `U_Q` picture.
- **Risk for expansive models.** A crossed product or groupoid ring whose letter-cylinder
  corners `χ_C R χ_C` are not matricially divisible has to kill the tame symbols in those
  corners by some other means, or it fails. This applies to Toeplitz subshifts and to the
  perfect-group actions of spark S1 in `research/artifacts/gq-deep-adelic-1-k-budget.md`.
