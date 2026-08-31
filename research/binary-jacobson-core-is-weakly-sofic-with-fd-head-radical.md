---
rg: 2
id: binary-jacobson-core-is-weakly-sofic-with-fd-head-radical
kind: claim
title: The binary Jacobson core is weakly sofic, but every exact finite-dimensional representation erases its head
artifacts:
  - research/binary-jacobson-weak-sofic-status-proof.md
distinct_from:
  one-balanced-actor-qutrit-bridge-is-jacobson-core: that identifies the finitely generated Jacobson elementary group and proves finite-quotient invisibility of a named head root; this determines the strongest standard metric-approximation consequence of its full exact sequence.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that asks for operator-MF invisibility in approximate representations; this proves only exact finite-dimensional invisibility and weak soficity, neither of which implies the requested normalized-HS conclusion.
  polynomial-qutrit-chart-has-hyperlinear-steinberg-lift: that proves hyperlinearity after replacing the one-sided-inverse ring by a polynomial ring; this records why the analogous conclusion does not follow for the Jacobson ring.
---

**ESTABLISHED.**  Put

```text
J=F_2<S,T | TS=1>,       Q=1-ST,
G=EL_28(J),              A=F_2[z,z^(-1)].
```

The symbol map gives an exact sequence

```text
1 -> L -> G -> EL_28(A) -> 1,                           (JWS1)
```

where

```text
L isomorphic to GL_fin(N x {1,...,28},F_2).
```

Consequently:

1. `L` is locally finite, hence amenable, sofic and weakly sofic.
2. `EL_28(A)` is finitely generated and residually finite.
3. By Glebsky's extension theorem, `G` is weakly sofic.
4. Every finite-dimensional unitary representation of `G` kills `L).
   In particular every such representation kills every head root
   `x_ij(S^r Q T^s)`.

The third statement is a genuine positive approximation result, but it does
not prove that `G` is sofic or hyperlinear.  The required permanence
direction is amenable-by-sofic: an amenable normal subgroup with sofic
quotient.  That direction remains open in general, even for finite cyclic
kernels.  Glebsky's weak-sofic target and normalized Hilbert--Schmidt
hyperlinearity are not known to coincide.

Thus the Jacobson candidate has a sharp status.  It is not an arbitrary
unknown group: it lies in the weakly sofic class and all of its exact matrix
representations factor through the residually finite Laurent symbol group.
Any nonhyperlinearity proof must therefore be quantitative.  It must show
that asymptotic normalized-HS representations cannot retain the regular
trace of a head root while their exact finite-dimensional limits erase the
whole finitary kernel.  Finite-quotient invisibility or the exact sequence
alone cannot supply that step.
