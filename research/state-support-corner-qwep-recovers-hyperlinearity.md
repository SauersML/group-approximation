---
rg: 2
id: state-support-corner-qwep-recovers-hyperlinearity
kind: claim
title: The expected bidual support corner is QWEP and recovers hyperlinearity
distinct_from:
  state-support-corner-exactifies-near-representation: that constructs the exact representation and Takesaki expectation in the state-support corner; this applies QWEP permanence and identifies exactly which approximation property follows.
  normal-state-free-near-representation-forces-factorization: that uses normality on the original B(H) to obtain Kirchberg factorization; this works for singular states but concludes only Connes embeddability.
  invariant-free-near-state-is-amenable-regular-cover: that constructs an amenable-trace C-star cover whose quotient is C*_r(G); this uses the von Neumann support corner and does not descend amenability through that quotient.
---

**ESTABLISHED.**  Under `(BSC1)--(BSC3)` of
`state-support-corner-exactifies-near-representation`, put

```text
M=B(H)**,   N=W*(rho(G)) subset sMs.
```

Then

```text
N ~= L(G) is QWEP.                                      (SCQ1)
```

If `G` is countable, `N` has separable predual, so `(SCQ1)` is equivalent to
a trace-preserving embedding

```text
L(G) -> R^omega.                                        (SCQ2)
```

Consequently `G` is hyperlinear.

This is a genuine consequence of the expected inclusion, but for a
Kahl--Schneider near-state it recovers an already known direction of their
hyperlinearity criterion.  It does **not** decide whether the binary Leavitt
unit group admits such a state.

The result is sharp in four useful senses.

1. It does not imply injectivity.  Take `G=F_2`.  This group is hyperlinear,
   so the Kahl--Schneider criterion supplies an invariant free near-state and
   the construction above supplies an expected support-corner copy of
   `L(F_2)`.  But `L(F_2)` is not injective.
2. It does not give a local u.c.p. splitting of the associated regular
   quotient.  For the same witness, put
   `A=C*(pi(F_2))`, let `tau=phi|_A`, and let
   `q:A->A/I_tau ~= C*_r(F_2)`.  The trace `tau` is amenable.  If `q` were
   locally u.c.p.-split, amenability would descend to the canonical trace of
   `C*_r(F_2)`, forcing `F_2` amenable, a contradiction.  Thus the expected
   von Neumann inclusion coexists with a non-locally-liftable C-star
   quotient.
3. It does not imply property `(T)` or property `(TT)/T`, again because the
   free-group example has neither.  For the binary Leavitt group those
   rigidity properties come from its elementary-group geometry, not from
   the support-corner expectation.
4. QWEP cannot be upgraded to WEP/injectivity merely from expectedness.
   Such an upgrade would already make the preceding `F_2` example
   injective.  Likewise, combining QWEP with the independently known
   property `(T)` of the Leavitt group does not create factorization:
   hyperlinear Kazhdan groups without Kirchberg factorization are known.

Therefore the singular-corner endpoint has a precise polarity:

```text
expected in s B(H)** s  =>  QWEP/CE  =>  hyperlinear,

but not injective, not locally split, and not rigid.     (SCQ3)
```

The Leavitt non-hyperlinearity route must exclude the near-state itself or
find extra structure forcing one of the unavailable upgrades; expectedness
is automatic and points in the hyperlinear direction.

DERIVATION
state-support-corner-qwep-proof
