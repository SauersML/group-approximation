---
rg: 2
id: strict-automata-give-injective-ca-with-skewed-site-marginals
kind: claim
title: A strict automaton yields an injective automaton on a product alphabet whose single-site output law is not uniform
distinct_from:
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that bounds the Rokhlin entropy of an amplified Bernoulli shift through measurable markers; this builds one explicit injective automaton, anchoring on a data track, whose single-site output law is not uniform, so the deficit is carried by a finite-radius generator.
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the open universal measure-preservation statement; this is the construction showing that a strict automaton already breaks the single-site law of some injective automaton.
artifacts:
  - research/artifacts/finitary-generation-single-site-criterion-2026-09-12.md
---

**ESTABLISHED** (artifact Section 2; route `skewed-site-marginal-construction-proof`; independent
re-derivation requested from `w3-vf-positive`).

Let `G` be a group, `A` a finite alphabet with `q = |A| >= 2`, and `tau` an injective, non-surjective
automaton on `A^G` whose image misses a pattern on the window `Omega`. Put `rho = q^(-|Omega Omega^-1|)`.
There is `c > 0` such that for every integer `k > (log 2)/(rho c)` some injective automaton `kappa` on
`(A^(k+1))^G` satisfies

    H( law of kappa(x)(e) under the uniform product measure ) < (k+1) log q .

**How `kappa` works.**
- Track `0` passes through unchanged and carries anchors: sites where it shows a fixed self-separating
  pattern on `Omega Omega^-1`.
- The other `k` tracks go through `tau`.
- Each anchored block is recoded by one fixed greedy injection that skews the law of one coordinate.
- `kappa` has an automaton left inverse.

**Consequences.**
- The time-zero partition of `kappa` generates and has entropy `< log |A^(k+1)|`, so a strict automaton
  gives a Bernoulli Rokhlin-entropy deficit through a finite-radius generator.
- `kappa` is an injective endomorphism with non-uniform site law. This is the input of
  `gottschalk-via-uniform-single-site-output-law`.
