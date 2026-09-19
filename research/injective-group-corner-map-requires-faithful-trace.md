---
rg: 2
id: injective-group-corner-map-requires-faithful-trace
kind: claim
title: An injective algebraic group-corner map requires a faithful tracial state
distinct_from:
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that needs only a unital homomorphism and uses the absence of CE traces; this isolates an additional prerequisite created by unnecessarily demanding injectivity.
  unique-trace-signed-corner-quotient-forces-nonhyperlinear: that studies a surjection in the opposite direction under trace uniqueness; this concerns an injection into a canonical group corner.
---

Let `B` be a unital star algebra and suppose that, for a group `Gamma` and a
nonzero algebraic projection `q in C[Gamma]`, there is an injective unital
star homomorphism

```text
Phi:B -> q C[Gamma] q,             Phi(1_B)=q.             (IGC1)
```

Then `B` has a faithful tracial state.  Namely, normalize the canonical
group trace on the corner and put

```text
sigma(b)=tau_Gamma(Phi(b))/tau_Gamma(q).                  (IGC2)
```

For `b != 0`, injectivity gives `Phi(b) != 0`, while faithfulness of the
regular trace gives

```text
sigma(b^*b)
 = ||Phi(b)||_(2,tau_Gamma)^2/tau_Gamma(q) > 0.           (IGC3)
```

Thus a universal theorem embedding arbitrary finitely presented tracial
star algebras into algebraic group corners is false without at least a
faithful-trace hypothesis.  Applied to the fixed MIP-star BCS source, the
published input supplies a tracial state and absence of CE traces, but does
not by itself assert that the universal BCS algebra has a faithful trace.
Passing to the null quotient of one trace repairs faithfulness for that
trace, and every trace on the quotient is still non-CE by pullback.  What is
not automatically preserved is finite presentation, which is precisely the
hypothesis needed by the proposed general embedding theorem.

This is also why injectivity is the wrong target for direct trace promotion:
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear` only needs a
unital homomorphism.  Requiring an embedding introduces `(IGC3)` without
strengthening the nonhyperlinearity conclusion.
