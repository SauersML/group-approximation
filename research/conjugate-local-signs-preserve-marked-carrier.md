---
rg: 2
id: conjugate-local-signs-preserve-marked-carrier
kind: claim
title: A Clifford tape may use conjugate local signs without losing marked spectral density
distinct_from:
  marked-hs-separation-forces-spectral-density: that extracts a positive carrier from one separated unitary; this shows every conjugate level word has an exactly transported carrier of the same trace.
  self-similar-clifford-quantum-expander-tape: that constructs and controls the whole tape; this removes only the unnecessary requirement that its local packet signs be one globally central word.
---

Let `t,w` be words and define the level words

```text
J_n=t^n w t^(-n).
```

For every matrix tuple `U`, with no relator assumption at all,

```text
J_n(U)=t(U)^n w(U)t(U)^(-n),
||J_n(U)-I||_2=||w(U)-I||_2.                                  (CLS1)
```

Moreover, for every Borel set `B` in the circle, functional calculus gives

```text
1_B(J_n(U))=t(U)^n 1_B(w(U))t(U)^(-n),                         (CLS2)
```

so all level carriers have exactly the same normalized trace. Consequently a
self-similar Clifford construction may use `J_n` as the central involution of
the **level-`n` local packet**, even though `w` is not central in the whole
group. Separation of the single marked word `w` supplies the same
positive-density carrier at every level for free.

For a ring-valued Heisenberg group with center `z(R)`, a compressor satisfying

```text
t z(c) t^(-1)=z(uc)
```

therefore transports `J_0=z(1)` to `J_n=z(u^n)`. This is exactly the moving
top-coefficient sign suggested by the truncated-polynomial Weyl tower. What
remains is to make the compressor compatible with the linear expander action
and the nested rank gates; global centrality of `J_0` is not required.
