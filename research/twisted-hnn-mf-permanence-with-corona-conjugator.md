---
rg: 2
id: twisted-hnn-mf-permanence-with-corona-conjugator
kind: claim
title: A regular MF realization with a corona conjugator for the edge passes to the HNN extension
artifacts:
  - research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md
distinct_from:
  regular-mf-tensor-sync-proves-twisted-rope-mf: that is the rope-specific theorem whose hypotheses are finite synchronization data for a product edge; this is a general HNN permanence consuming one abstract corona conjugator, of which the tensor construction is one producer.
  crossed-product-by-corona-inner-automorphism-is-mf: that assumes a corona-inner automorphism of the whole base algebra; this assumes only a partial conjugator between two edge subalgebras and no automorphism extension.
  hnn-form-of-gkmp-attempt: that seeks reduced-norm strong-convergence MF of the reduced C-star algebra; this is the operator-MF and regular-realization statement, where the universal HNN algebra replaces every freeness estimate.
---

**ESTABLISHED.**  Let

```text
R = < G, t | t s t^-1 = theta(s), s in S >
```

be a group HNN extension of a countable group `G` with associated subgroups
`S` and `theta(S)`.  Suppose

1. `G` has a regular operator-MF realization `(A, rho, tr)`: `A` separable
   unital MF, `rho : G -> U(A)` with `tr(rho(g)) = delta_{g,1}` for a
   tracial state `tr`; and
2. some embedding `iota : A -> prod M_n / sum M_n` admits a unitary `W`
   with `W iota(rho(s)) W* = iota(rho(theta(s)))` for every `s in S`.

Then `R` has a regular operator-MF realization; in particular `R` is
operator-MF.  The central case `theta = id`, `W = 1` recovers
[[regular-mf-central-hnn-closure]] with no additional input.

The proof (route [[twisted-hnn-corona-conjugator-proof]]) has no freeness
estimate, no reduced HNN normal form, and no strong convergence: the
universal C-star HNN algebra of `C*(iota rho(G))` is MF by Shulman's
amalgam criterion applied to a self-contained corner realization, and the
group injects because the regular trace of the base plus the left regular
representation of `R` produce a representation of the universal algebra
extending `lambda_R`.  Full details in the artifact, Section 3.

The hypotheses are exactly what the finite-presentation MF compiler
produces at both of its HNN steps, so this theorem yields a second,
independently verified proof of
[[regular-mf-tensor-sync-proves-twisted-rope-mf]] via
[[regular-mf-tensor-sync-via-corona-conjugator]].
