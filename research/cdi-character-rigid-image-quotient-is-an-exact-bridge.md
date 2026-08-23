---
rg: 2
id: cdi-character-rigid-image-quotient-is-an-exact-bridge
kind: claim
title: Character rigidity of the actual CDI image quotient is an exact canonical-trace bridge
distinct_from:
  factor-universality-character-rigidity-implies-nonhyperlinear: that assumes one source group has both universality and rigidity; this needs rigidity only for the image quotient of one universal representation.
  cdi-noncartan-bridge-has-two-exact-gates: that characterizes compilation through a finite central twisted sector using vanishing and torsion; this obtains an untwisted canonical group factor directly from factor-character rigidity.
  ah-groups-fail-regular-fd-character-rigidity: that rules out rigidity for the acylindrically hyperbolic source; this permits its particular representation image to be a different rigid quotient.
---

Let `M_0` be a separable non-Connes-embeddable tracial algebra, and apply
Chifan--Drimbe--Ioana factor-representation universality to obtain

```text
pi:H -> U(Q),        pi(H)''=Q,        M_0 subset Q.     (CIQ1)
```

Put `Lambda=H/ker(pi)`.  Suppose every nonregular extremal character of
`Lambda` has a Connes-embeddable GNS factor.  Then

```text
Q ~= L(Lambda)                                             (CIQ2)
```

trace-preservingly, so `Lambda` is nonhyperlinear.

This is the optimal character bridge for the CDI representation.  It does
not require character rigidity of the acylindrically hyperbolic source
`H`; it requires it only after the *actual*, representation-dependent
kernel has been divided out.  Conversely, replacing `Lambda` by some other
chosen character-rigid quotient of `H` is invalid unless one proves that
its kernel lies in `ker(pi)`.

The condition holds, for example, if the only extremal characters of
`Lambda` are regular or finite dimensional, or more generally if every
nonregular factorial character is von Neumann amenable.  Thus a theorem
forcing the CDI image quotient into either of those rigidity classes would
immediately finish the nonhyperlinear-group problem.

