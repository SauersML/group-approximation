---
rg: 2
id: stw09-trace-coherent-model-criterion-proof
kind: route
title: Use faithfulness after passing compatible traces to the AF limit
target: stw09-trace-preserving-af-embedding-iff-trace-coherent-models
requires: []
---

Given a trace-coherent system, let `E=lim(F_n,alpha_n)`.  Summable coherence
and contractivity give a pointwise limit `Phi:A->E`, and asymptotic
multiplicativity makes `Phi` a unital homomorphism exactly as in
`stw08-coherent-fd-model-criterion-proof`.  Exact compatibility of the
`sigma_n` defines a trace `sigma` on `E`.  Passing to the limit in
`sigma_n phi_n(a)` gives `sigma(Phi(a))=tau(a)`.  Since `tau` is faithful, if
`Phi(a)=0`, then

```text
tau(a* a)=sigma(Phi(a* a))=0,
```

so `a=0`; hence `Phi` is an AF embedding.

Conversely, suppose `Phi:A->E` is an AF embedding and `sigma Phi=tau`.
Choose increasing finite-dimensional stages `F_n` with dense union and u.c.p.
retractions `P_n:E->F_n` as in the proof of the untraced criterion.  Put
`phi_n=P_n Phi` and `sigma_n=sigma|F_n`.  The traces are exactly compatible.
After passing to stages which approximate growing finite subsets of `Phi(A)`
with summable error, the maps are summably coherent and asymptotically
multiplicative.  Norm approximation also gives

```text
sigma_n phi_n(a) -> sigma Phi(a)=tau(a).
```

This proves the equivalence.  Quasidiagonality of `tau` alone gives unrelated
matricial maps; it does not provide either of the two interstage compatibility
conditions above.
