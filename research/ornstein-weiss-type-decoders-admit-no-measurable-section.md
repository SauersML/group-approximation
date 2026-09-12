---
rg: 2
id: ornstein-weiss-type-decoders-admit-no-measurable-section
kind: claim
title: A decoder that recovers a uniform input functional as a difference along one group element has no measurable equivariant section, so inverting Ornstein--Weiss codes never compresses
distinct_from:
  xor-lift-of-bernoulli-has-positive-fiber-entropy: that computes the fiber entropy of the invariant lift through the XOR automaton; this shows that no Borel equivariant section of any two-term difference decoder exists, over any group, whatever coordinates the section reads.
  homomorphic-codes-cannot-compress-bernoulli-shifts: that kills codes whose encoder is a homomorphism; this kills codes whose decoder has a two-term difference row, with an arbitrary Borel encoder.
  non-enlarging-sofic-window-cascades-cannot-compress: that constrains encoders presented as cascades of stages; this constrains the decoder.
artifacts:
  - research/artifacts/ornstein-weiss-decoder-sections-2026-09-12.md
---

Let `G` be countable, `A, B` finite, `a` in `G`, `n >= 2`, `lambda: A -> Z/n` pushing uniform to uniform, and
`beta: B -> Z/n`. Then no Borel equivariant `tau: A^G -> B^G` satisfies

    lambda(x(1)) = beta(tau(x)(1)) - beta(tau(x)(a))      for mu_A-almost every x.

So a map `sigma: B^G -> A^G` with a row `lambda(sigma(y)(g)) = beta(y(g)) - beta(y(ga))` has no measurable
equivariant section, and no almost everywhere injective code has such a decoder.

**Ornstein--Weiss.** The map `phi(y)(g) = (y(g) + y(ga), y(g) + y(gb))` has no measurable equivariant section over
any group containing `<a, b>`. Over `U = L_(F_2)(1,2)^x` the fiber of the ascended map is `(Z/2)^(U/F_2)`, and a
section could read the rigid defect or any other coset. It still does not exist, and the same holds with `b`
replaced by the defect. Inverting Ornstein--Weiss codes therefore gives no compression over `U`.

An Ornstein--Weiss encoding stage is never injective for uniform input (it kills coset indicators), so it cannot
appear as a stage of an almost everywhere injective cascade. As a parallel track it is just an enlarging stage.

**Proof idea.** Put `p(x) = beta(tau(x)(1))`. Equivariance turns the identity into
`p(x) - p(a^-1.x) = lambda(x(1))`.
- For finite order, summing around the orbit of `a` gives a contradiction.
- For infinite order, `omega^(eps + p(x))` is invariant under the skew product `(x, eps) -> (a^-1.x, eps + lambda(x(1)))`.
  Partial sums conjugate that skew product to a Bernoulli shift times a Bernoulli shift, so it is ergodic, and
  the invariant function cannot be constant.

Proof: Sections 1–2 of the artifact, route `ornstein-weiss-type-decoder-sections-proof`.

## Attempts

- **Rows with three or more terms** along `a` and the defect `d` give a multi-shift functional equation with no
  single skew product. They are open (artifact Section 4).

**ESTABLISHED 2026-09-12** by [[ornstein-weiss-type-decoder-sections-proof]]. Verification requested from
w3-vf-nonlinear.
