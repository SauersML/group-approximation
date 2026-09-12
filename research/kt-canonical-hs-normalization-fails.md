---
rg: 2
id: kt-canonical-hs-normalization-fails
kind: claim
title: Some Connes-embeddable model of the Kun--Thom actor, with any trace, has a non-normalized Gamma-commutant
invalidates: [kt-pair-non-hyperlinear-commutant]
distinct_from:
  kt-centralizer-normalization-hs: that is the universal normalization statement over all trace-preserving representations; this is the negation of its Connes-embeddable instance, with no trace condition, and any such counterexample answers Question 3.4.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**OPEN.**  For the Kun--Thom Theorem E pair `Gamma < G`, there exist a
Connes-embeddable finite tracial algebra `M` and a homomorphism
`sigma: G -> U(M)`, with no condition on `tau o sigma` and `sigma` not necessarily injective, such that

```text
R = sigma(Gamma)' cap M   is not normalized by sigma(G).
```

**Stakes: this is a fork between the two program goals.**
- If established, `hyperlinear-nonsofic-from-canonical-hs-normalization-failure`
  produces a hyperlinear nonsofic binary coset wreath and answers Pestov 3.4.
  It also refutes `kt-centralizer-normalization-hs`, killing
  `kt-pair-non-hyperlinear-commutant`.
- Its negation, the canonical instance of `kt-centralizer-normalization-hs`,
  already proves the Kun--Thom wreath non-hyperlinear.

The claim is equivalent to hyperlinearity of `W_K` for some `K` with
`Gamma <= K <= G`, `N = <<Gamma>>_G` not in `K`.
- Forward direction: the route below.
- Converse: a hyperlinear `W_K` gives, through relative embeddability, a
  canonical model whose `K`-lamp lies in `R` and whose commutation stabilizer
  is `K`.  Normalization would force `N <= K`.

It is strictly weaker than hyperlinearity of `W = W_Gamma`, since any
intermediate `K` suffices.

## Attempts

- **Finite and profinite models.** Dead.  A profinitely closed `K >= Gamma`
  contains `N` (`infranormal-compact-closure-normal`), so separable
  intermediate subgroups never qualify.
- **Sofic-action permanence for `G action G/K`.** Dead for every qualifying
  `K`.  Kun--Thom Theorem C applies to `Gamma <= G` regardless of `K`, and the
  coordinate at the coset `K` is `Gamma`-invariant but not `G`-invariant, so
  the Bernoulli action over `G/K` is never sofic.
- **One-compressor subgroups `K = <Gamma,t>`.** Qualify (`N` is not in
  `<Gamma,t>`) and are not Kazhdan, but the action is still nonsofic by the
  previous item.  A model must be native, e.g. extend the one-compressor
  permutation model of `<Gamma,t>` to all of `G` inside a II_1 envelope.
