---
rg: 2
id: unrestricted-algebraic-envelope-equivalence-proof
kind: route
title: Apply Pontryagin duality forward and the trivial compact group backward
target: unrestricted-algebraic-envelope-equals-nonhyperlinearity
requires: []
---

Put `A=hat K`.  Fourier transform gives the canonical trace-preserving
isomorphism

```text
L^infinity(K) rtimes Lambda = L(A rtimes Lambda).
```

If the left side contains a non-CE tracial algebra, then it is non-CE because
Connes embeddability passes to von Neumann subalgebras.  Hence the canonical
group trace of `A rtimes Lambda` is non-CE, so `A rtimes Lambda` is
non-hyperlinear.  This is the forward implication already isolated in
`algebraic-envelope-principle`.

Conversely, given a countable non-hyperlinear group `G`, take the one-point
compact abelian group `K={e}` and `Lambda=G`.  Then

```text
L^infinity(K) rtimes Lambda = C rtimes G = L(G),
```

which is non-CE and contains itself trace-preservingly.  The trivial-base
construction preserves finite generation, recursive presentation, and
explicitness.  Thus the relaxed envelope statement does not lower the
difficulty of `non-hyperlinear-group`.
